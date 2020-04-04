package org.checkerframework.checker.mungo.annotators

import com.sun.source.tree.Tree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.checker.mungo.qualifiers.MungoBottom
import org.checkerframework.checker.mungo.qualifiers.MungoInternalInfo
import org.checkerframework.checker.mungo.qualifiers.MungoUnknown
import org.checkerframework.checker.mungo.typecheck.*
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.dataflow.cfg.node.Node
import org.checkerframework.framework.flow.CFAbstractAnalysis
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory
import org.checkerframework.framework.type.QualifierHierarchy
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator
import org.checkerframework.framework.type.treeannotator.TreeAnnotator
import org.checkerframework.framework.type.typeannotator.DefaultQualifierForUseTypeAnnotator
import org.checkerframework.framework.util.GraphQualifierHierarchy
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.javacutil.Pair
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.VariableElement

class MungoAnnotatedTypeFactory(checker: MungoChecker) : GenericAnnotatedTypeFactory<MungoValue, MungoStore, MungoTransfer, MungoAnalysis>(checker) {

  private val c = checker

  init {
    postInit()
  }

  override fun getStoreAfter(node: Node): MungoStore? {
    return if (!analysis.isRunning) {
      // Fix assertion error "assert transferInput != null" on AnalysisResult#runAnalysisFor
      flowResult.getStoreAfter(node)
    } else {
      super.getStoreAfter(node)
    }
  }

  override fun createFlowAnalysis(fieldValues: List<Pair<VariableElement, MungoValue>>): MungoAnalysis {
    return MungoAnalysis(c, this, fieldValues)
  }

  override fun createFlowTransferFunction(analysis: CFAbstractAnalysis<MungoValue, MungoStore, MungoTransfer>): MungoTransfer {
    return MungoTransfer(c, analysis as MungoAnalysis)
  }

  override fun createTreeAnnotator(): TreeAnnotator {
    // TreeAnnotator that adds annotations to a type based on the contents of a tree
    return ListTreeAnnotator(MungoTreeAnnotator(c, this), super.createTreeAnnotator())
  }

  override fun createDefaultForUseTypeAnnotator(): DefaultQualifierForUseTypeAnnotator {
    return MungoDefaultQualifierForUseTypeAnnotator(c, this)
  }

  override fun createSupportedTypeQualifiers(): Set<Class<out Annotation>> {
    // Do NOT include @MungoTypestate or @MungoState or @MungoNullable here
    return setOf(MungoBottom::class.java, MungoInternalInfo::class.java, MungoUnknown::class.java)
  }

  override fun createQualifierHierarchy(factory: MultiGraphQualifierHierarchy.MultiGraphFactory): QualifierHierarchy {
    return MungoQualifierHierarchy(factory, MungoBottomType.SINGLETON.buildAnnotation(checker.processingEnvironment))
  }

  private inner class MungoQualifierHierarchy(f: MultiGraphFactory, bottom: AnnotationMirror) : GraphQualifierHierarchy(f, bottom) {
    override fun isSubtype(subAnno: AnnotationMirror, superAnno: AnnotationMirror): Boolean {
      val sub = MungoUtils.mungoTypeFromAnnotation(subAnno)
      val sup = MungoUtils.mungoTypeFromAnnotation(superAnno)
      return sub.isSubtype(sup)
    }

    override fun leastUpperBound(a1: AnnotationMirror, a2: AnnotationMirror): AnnotationMirror {
      val type1 = MungoUtils.mungoTypeFromAnnotation(a1)
      val type2 = MungoUtils.mungoTypeFromAnnotation(a2)
      return type1.leastUpperBound(type2).buildAnnotation(checker.processingEnvironment)
    }

    override fun greatestLowerBound(a1: AnnotationMirror, a2: AnnotationMirror): AnnotationMirror {
      val type1 = MungoUtils.mungoTypeFromAnnotation(a1)
      val type2 = MungoUtils.mungoTypeFromAnnotation(a2)
      return type1.intersect(type2).buildAnnotation(checker.processingEnvironment)
    }
  }

  fun replaceWithInferredInfo(tree: Tree, type: AnnotatedTypeMirror) {
    val value = getInferredValueFor(tree)
    if (value != null) {
      type.replaceAnnotation(value.info.buildAnnotation(checker.processingEnvironment))
    }
  }

  // This is called in both MungoTreeAnnotator#visitVariable and MungoDefaultQualifierForUseTypeAnnotator#visitDeclared
  // For some reason, it must be called in "visitDeclared" as well...
  // Nonetheless, "visitVariable" is always called for both method arguments and variable declarations,
  // so we only report errors in that case, which provides "tree", for error location.
  fun visitMungoAnnotations(type: AnnotatedTypeMirror.AnnotatedDeclaredType, tree: Tree?) {
    val element = type.underlyingType.asElement()
    val stateAnno = type.underlyingType.annotationMirrors.find { AnnotationUtils.areSameByName(it, MungoUtils.mungoStateName) }
    val nullableAnno = type.underlyingType.annotationMirrors.find { AnnotationUtils.areSameByName(it, MungoUtils.mungoNullableName) }

    val stateTypes = run {
      val graph = c.utils.visitClassSymbol(element)
      if (graph == null) {
        if (stateAnno != null && tree != null) {
          c.utils.err("@MungoState has no meaning since this type has no protocol", tree)
        }
        MungoNoProtocolType.SINGLETON
      } else {
        val states = if (stateAnno == null) {
          graph.getAllConcreteStates()
        } else {
          val stateNames = AnnotationUtils.getElementValueArray(stateAnno, "value", String::class.java, false)
          if (tree != null) {
            c.utils.checkStates(graph.file, stateNames, tree)
          }
          graph.getAllConcreteStates().filter { stateNames.contains(it.name) }
        }
        MungoUnionType.create(states.map { MungoStateType.create(graph, it) })
      }
    }

    val maybeNullableType = if (nullableAnno == null) MungoBottomType.SINGLETON else MungoNullType.SINGLETON

    type.replaceAnnotation(MungoUnionType.create(listOf(stateTypes, maybeNullableType)).buildAnnotation(checker.processingEnvironment))
  }
}
