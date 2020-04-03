package org.checkerframework.checker.mungo.annotators

import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.checker.mungo.qualifiers.MungoBottom
import org.checkerframework.checker.mungo.qualifiers.MungoInternalInfo
import org.checkerframework.checker.mungo.qualifiers.MungoUnknown
import org.checkerframework.checker.mungo.typecheck.MungoBottomType
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.dataflow.cfg.node.Node
import org.checkerframework.framework.flow.CFAbstractAnalysis
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory
import org.checkerframework.framework.type.QualifierHierarchy
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator
import org.checkerframework.framework.type.treeannotator.TreeAnnotator
import org.checkerframework.framework.type.typeannotator.DefaultQualifierForUseTypeAnnotator
import org.checkerframework.framework.util.GraphQualifierHierarchy
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy
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
    // Do NOT include @MungoTypestate or @MungoState here
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
}
