package org.checkerframework.checker.mungo.annotators

import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.MungoAnalysis
import org.checkerframework.checker.mungo.analysis.MungoStore
import org.checkerframework.checker.mungo.analysis.MungoTransfer
import org.checkerframework.checker.mungo.analysis.MungoValue
import org.checkerframework.checker.mungo.qualifiers.MungoBottom
import org.checkerframework.checker.mungo.qualifiers.MungoInfo
import org.checkerframework.checker.mungo.qualifiers.MungoUnknown
import org.checkerframework.checker.mungo.typecheck.MungoTypecheck
import org.checkerframework.framework.flow.CFAbstractAnalysis
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory
import org.checkerframework.framework.type.QualifierHierarchy
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator
import org.checkerframework.framework.type.treeannotator.TreeAnnotator
import org.checkerframework.framework.type.typeannotator.DefaultQualifierForUseTypeAnnotator
import org.checkerframework.framework.util.GraphQualifierHierarchy
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy
import org.checkerframework.javacutil.AnnotationBuilder
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.javacutil.Pair
import java.util.*
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.VariableElement

class MungoAnnotatedTypeFactory(checker: MungoChecker) : GenericAnnotatedTypeFactory<MungoValue, MungoStore, MungoTransfer, MungoAnalysis>(checker) {

  private val annoBOTTOM = AnnotationBuilder.fromClass(elements, MungoBottom::class.java)
  private val annoINFO = AnnotationBuilder.fromClass(elements, MungoInfo::class.java)
  private val annoUNKNOWN = AnnotationBuilder.fromClass(elements, MungoUnknown::class.java)

  override fun createFlowAnalysis(fieldValues: List<Pair<VariableElement, MungoValue>>): MungoAnalysis {
    return MungoAnalysis(checker as MungoChecker, this, fieldValues)
  }

  override fun createFlowTransferFunction(analysis: CFAbstractAnalysis<MungoValue, MungoStore, MungoTransfer>): MungoTransfer {
    return MungoTransfer(checker as MungoChecker, analysis as MungoAnalysis)
  }

  override fun createTreeAnnotator(): TreeAnnotator {
    // TreeAnnotator that adds annotations to a type based on the contents of a tree
    return ListTreeAnnotator(MungoTreeAnnotator(checker as MungoChecker, this), super.createTreeAnnotator())
  }

  override fun createDefaultForUseTypeAnnotator(): DefaultQualifierForUseTypeAnnotator {
    return MungoDefaultQualifierForUseTypeAnnotator(checker as MungoChecker, this)
  }

  override fun createSupportedTypeQualifiers(): Set<Class<out Annotation>> {
    val set = HashSet<Class<out Annotation>>()
    // Do NOT include @MungoTypestate here
    Collections.addAll(set, MungoBottom::class.java, MungoInfo::class.java, MungoUnknown::class.java)
    return set
  }

  override fun createQualifierHierarchy(factory: MultiGraphQualifierHierarchy.MultiGraphFactory): QualifierHierarchy {
    return MungoQualifierHierarchy(factory, annoBOTTOM)
  }

  private inner class MungoQualifierHierarchy(f: MultiGraphFactory, bottom: AnnotationMirror) : GraphQualifierHierarchy(f, bottom) {
    // BOTTOM <: STATE <: UNKNOWN
    override fun isSubtype(subAnno: AnnotationMirror, superAnno: AnnotationMirror): Boolean {
      if (AnnotationUtils.areSameByName(subAnno, annoBOTTOM)) {
        return true
      }
      if (AnnotationUtils.areSameByName(subAnno, annoINFO)) {
        return if (AnnotationUtils.areSameByName(superAnno, annoINFO)) {
          MungoTypecheck.isSubType(subAnno, superAnno)
        } else AnnotationUtils.areSameByName(superAnno, annoUNKNOWN)
      }
      return if (AnnotationUtils.areSameByName(subAnno, annoUNKNOWN)) {
        AnnotationUtils.areSameByName(superAnno, annoUNKNOWN)
      } else false
    }
  }

  init {
    postInit()
  }
}
