package org.checkerframework.checker.mungo.internal;

import javax.lang.model.element.AnnotationMirror;

public class MungoTypecheck {

  // pre: "sub" and "sup" @MungoInfo annotations
  public static boolean isSubType(AnnotationMirror sub, AnnotationMirror sup) {
    return isSubType(MungoUtils.castAnnotation(sub), MungoUtils.castAnnotation(sup));
  }

  public static boolean isSubType(MungoTypeInfo sub, MungoTypeInfo sup) {
    return sub.graph == sup.graph && sup.states.containsAll(sub.states);
  }

}
