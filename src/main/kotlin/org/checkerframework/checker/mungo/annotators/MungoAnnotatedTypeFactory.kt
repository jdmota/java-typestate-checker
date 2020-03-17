package org.checkerframework.checker.mungo.annotators

import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.MungoAnalysis
import org.checkerframework.checker.mungo.analysis.MungoStore
import org.checkerframework.checker.mungo.analysis.MungoTransfer
import org.checkerframework.checker.mungo.analysis.MungoValue
import org.checkerframework.checker.mungo.qualifiers.MungoBottom
import org.checkerframework.checker.mungo.qualifiers.MungoInfo
import org.checkerframework.checker.mungo.qualifiers.MungoUnknown
import org.checkerframework.dataflow.analysis.AnalysisResult
import org.checkerframework.framework.flow.CFAbstractAnalysis
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
    // Do NOT include @MungoTypestate here
    return setOf(MungoBottom::class.java, MungoInfo::class.java, MungoUnknown::class.java)
  }

  override fun createQualifierHierarchy(factory: MultiGraphQualifierHierarchy.MultiGraphFactory): QualifierHierarchy {
    return MungoQualifierHierarchy(factory, c.utils.bottomAnnotation)
  }

  private inner class MungoQualifierHierarchy(f: MultiGraphFactory, bottom: AnnotationMirror) : GraphQualifierHierarchy(f, bottom) {
    // BOTTOM <: INFO <: UNKNOWN
    override fun isSubtype(subAnno: AnnotationMirror, superAnno: AnnotationMirror): Boolean {
      if (AnnotationUtils.areSameByName(subAnno, c.utils.bottomAnnotation)) {
        return true
      }
      if (AnnotationUtils.areSameByName(subAnno, c.utils.infoAnnotation)) {
        return if (AnnotationUtils.areSameByName(superAnno, c.utils.infoAnnotation)) {
          AnnotationUtils.sameElementValues(superAnno, subAnno)
        } else {
          AnnotationUtils.areSameByName(superAnno, c.utils.unknownAnnotation)
        }
      }
      return if (AnnotationUtils.areSameByName(subAnno, c.utils.unknownAnnotation)) {
        AnnotationUtils.areSameByName(superAnno, c.utils.unknownAnnotation)
      } else false
    }
  }
}
