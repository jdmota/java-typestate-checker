package org.checkerframework.checker.mungo.analysis

import org.checkerframework.checker.mungo.typecheck.MungoTypeInfo
import org.checkerframework.checker.mungo.typecheck.MungoTypecheck
import org.checkerframework.framework.flow.CFAbstractValue
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.TypeElement
import javax.lang.model.type.TypeMirror

class MungoValue(analysis: MungoAnalysis, annotations: Set<AnnotationMirror>, underlyingType: TypeMirror) : CFAbstractValue<MungoValue>(analysis, annotations, underlyingType) {

  private val a = analysis
  private var computed = false

  private var previousInfo: MungoTypeInfo? = null
  private var info: MungoTypeInfo? = null

  constructor(oldVal: MungoValue, info: MungoTypeInfo, prev: MungoTypeInfo?) : this(oldVal.analysis as MungoAnalysis, oldVal.annotations, oldVal.underlyingType) {
    this.previousInfo = prev
    this.info = info
    this.computed = true
  }

  constructor(oldVal: MungoValue, info: MungoTypeInfo) : this(oldVal, info, null)

  // If we have no info stored, compute one MungoTypeInfo object with all states
  fun getInfo(): MungoTypeInfo? {
    if (!computed) {
      val graph = a.getUtils().getGraphFromAnnotations(annotations)
      setInfo(if (graph == null) null else MungoTypeInfo(graph, graph.getAllConcreteStates()))
    }
    return info
  }

  private fun setInfo(newInfo: MungoTypeInfo?): MungoValue {
    info = newInfo
    computed = true
    return this
  }

  fun getPrevInfo(): MungoTypeInfo? {
    return previousInfo
  }

  override fun toString(): String {
    return "MungoValue{info=${getInfo()}, prev=$previousInfo, annos=${annotations.joinToString {
      (it.annotationType.asElement() as TypeElement).simpleName
    }}, type=$underlyingType}"
  }

  /*
  FIXME
  leastUB args:
  MungoValue{info=null, prev=null, annos=MungoBottom, type=<nulltype>}
  MungoValue{info=MungoTypeInfo[State{name=HasNext}], prev=null, annos=MungoInfo, type=JavaIterator}
  leastUB res: MungoValue{info=MungoTypeInfo[State{name=end}, State{name=HasNext}, State{name=Next}], prev=null, annos=MungoInfo, type=JavaIterator}
   */

  override fun leastUpperBound(other: MungoValue?): MungoValue {
    println("leastUB args: \n$this\n$other")
    val thisInfo = getInfo()
    val otherInfo = other?.getInfo()
    val r = super.leastUpperBound(other)
    if (thisInfo == null || otherInfo == null) {
      println("leastUB res: $r\n")
      return r
    }
    r.setInfo(MungoTypecheck.leastUpperBound(thisInfo, otherInfo))
    println("leastUB res: $r\n")
    return r
  }

  override fun mostSpecific(other: MungoValue?, backup: MungoValue?): MungoValue {
    println("mostSpecific args: \n$this\n$other")
    val thisInfo = getInfo()
    val otherInfo = other?.getInfo()
    val r = super.mostSpecific(other, backup)
    when {
      thisInfo == null -> r.setInfo(otherInfo)
      otherInfo == null -> r.setInfo(thisInfo)
      else -> r.setInfo(MungoTypecheck.mostSpecific(thisInfo, otherInfo))
    }
    println("mostSpecific res: $r\n")
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
