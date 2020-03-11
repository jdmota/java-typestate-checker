package org.checkerframework.checker.mungo.typecheck

import org.checkerframework.checker.mungo.utils.MungoUtils.Companion.castAnnotation
import javax.lang.model.element.AnnotationMirror

object MungoTypecheck {
  // pre: "sub" and "sup" @MungoInfo annotations
  fun isSubType(sub: AnnotationMirror, sup: AnnotationMirror): Boolean {
    return isSubType(castAnnotation(sub), castAnnotation(sup))
  }

  fun isSubType(sub: MungoTypeInfo, sup: MungoTypeInfo): Boolean {
    return sub.graph === sup.graph && sup.states.containsAll(sub.states)
  }
}
