package org.checkerframework.checker.mungo.analysis

import org.checkerframework.checker.mungo.typecheck.MungoType
import org.checkerframework.checker.mungo.typecheck.MungoTypecheck
import org.checkerframework.framework.flow.CFAbstractValue
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.TypeElement
import javax.lang.model.type.TypeMirror

class MungoValue(analysis: MungoAnalysis, annotations: Set<AnnotationMirror>, underlyingType: TypeMirror) : CFAbstractValue<MungoValue>(analysis, annotations, underlyingType) {

  private val a = analysis

  private var previousInfo: MungoType? = null
  private var info: MungoType? = null

  constructor(oldVal: MungoValue, info: MungoType, prev: MungoType?) : this(oldVal.analysis as MungoAnalysis, oldVal.annotations, oldVal.underlyingType) {
    this.previousInfo = prev
    this.info = info
  }

  constructor(oldVal: MungoValue, info: MungoType) : this(oldVal, info, null)

  // If we have no info stored, compute one MungoTypeInfo object with all states
  fun getInfo(): MungoType {
    val currInfo = info
    if (currInfo == null) {
      val newInfo = a.getUtils().mungoTypeFromAnnotations(annotations)
      info = newInfo
      return newInfo
    }
    return currInfo
  }

  fun getPrevInfo(): MungoType? {
    return previousInfo
  }

  override fun toString(): String {
    return "MungoValue{info=${getInfo()}, prev=$previousInfo, annos=${annotations.joinToString {
      (it.annotationType.asElement() as TypeElement).simpleName
    }}, type=$underlyingType}"
  }

  override fun leastUpperBound(other: MungoValue?): MungoValue {
    if (other == null) {
      return this
    }
    val thisInfo = getInfo()
    val otherInfo = other.getInfo()
    val r = super.leastUpperBound(other)
    r.info = MungoTypecheck.leastUpperBound(thisInfo, otherInfo)
    return r
  }

  override fun mostSpecific(other: MungoValue?, backup: MungoValue?): MungoValue? {
    if (other == null) {
      return this
    }
    val thisInfo = getInfo()
    val otherInfo = other.getInfo()
    val r = super.mostSpecific(other, backup)
    r.info = MungoTypecheck.mostSpecific(thisInfo, otherInfo)
    if (r.info == null) {
      return null
    }
    return r
  }

  override fun hashCode(): Int {
    var result = super.hashCode()
    result = 31 * result + info.hashCode()
    return result
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other !is MungoValue) return false
    return super.equals(other) && info == other.info
  }

}
