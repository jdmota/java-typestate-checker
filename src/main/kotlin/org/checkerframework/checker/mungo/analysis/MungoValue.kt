package org.checkerframework.checker.mungo.analysis

import org.checkerframework.checker.mungo.typecheck.MungoTypeInfo
import org.checkerframework.framework.flow.CFAbstractValue
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.type.TypeMirror

class MungoValue(analysis: MungoAnalysis, annotations: Set<AnnotationMirror>, underlyingType: TypeMirror) : CFAbstractValue<MungoValue>(analysis, annotations, underlyingType) {

  var previousTypeInfo: MungoTypeInfo? = null

  override fun toString(): String {
    return if (previousTypeInfo == null)
      "MungoValue{annotations=$annotations, underlyingType=$underlyingType}"
    else
      "MungoValue{annotations=$annotations, underlyingType=$underlyingType, previous=$previousTypeInfo}"
  }
}
