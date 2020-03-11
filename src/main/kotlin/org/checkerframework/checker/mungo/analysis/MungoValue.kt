package org.checkerframework.checker.mungo.analysis

import org.checkerframework.framework.flow.CFAbstractValue
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.type.TypeMirror

class MungoValue(analysis: MungoAnalysis, annotations: Set<AnnotationMirror>, underlyingType: TypeMirror) : CFAbstractValue<MungoValue>(analysis, annotations, underlyingType) {
  override fun toString(): String {
    return ("MungoValue{"
      + "annotations="
      + annotations
      + ", underlyingType="
      + underlyingType
      + '}')
  }
}
