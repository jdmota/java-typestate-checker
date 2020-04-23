package org.checkerframework.checker.mungo.analysis

import org.checkerframework.checker.mungo.typecheck.MungoType
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.framework.flow.CFAbstractValue
import org.checkerframework.javacutil.AnnotationUtils
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.TypeElement
import javax.lang.model.type.TypeMirror

// Filter Mungo annotations out
private fun filter(value: MungoValue) = value.annotations.filterNot { MungoUtils.isMungoAnnotation(it) }

class MungoValue(analysis: MungoAnalysis, annotations: Set<AnnotationMirror>, underlyingType: TypeMirror) : CFAbstractValue<MungoValue>(analysis, annotations, underlyingType) {

  private val a = analysis

  val info: MungoType = MungoUtils.mungoTypeFromAnnotations(annotations)

  constructor(prevValue: MungoValue, newInfo: MungoType) : this(prevValue.a, filter(prevValue).plus(newInfo.buildAnnotation(prevValue.a.typeFactory.processingEnv)).toSet(), prevValue.underlyingType)

  override fun toString(): String {
    return "MungoValue{info=$info, annos=${annotations.joinToString {
      (it.annotationType.asElement() as TypeElement).simpleName
    }}, type=$underlyingType}"
  }

  override fun leastUpperBound(other: MungoValue?): MungoValue {
    if (other == null) {
      return this
    }
    val result = super.leastUpperBound(other)
    val newInfo = info.leastUpperBound(other.info)
    return MungoValue(result, newInfo)
  }

  override fun widenUpperBound(other: MungoValue?): MungoValue {
    if (other == null) {
      return this
    }
    val result = super.widenUpperBound(other)
    val newInfo = info.leastUpperBound(other.info)
    return MungoValue(result, newInfo)
  }

  override fun mostSpecific(other: MungoValue?, backup: MungoValue?): MungoValue? {
    if (other == null) {
      return this
    }
    val result = super.mostSpecific(other, backup)
    val newInfo = info.mostSpecific(other.info) ?: return null
    return MungoValue(result ?: this, newInfo)
  }

  override fun hashCode(): Int {
    var result = super.hashCode()
    result = 31 * result + info.hashCode()
    return result
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other !is MungoValue) return false
    if (info != other.info) return false
    // Adapted from CFAbstractValue
    return (getUnderlyingType() === other.underlyingType ||
      a.c.typeUtils.isSameType(underlyingType, other.underlyingType)) &&
      AnnotationUtils.areSame(filter(this), filter(other))
  }

}
