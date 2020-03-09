package org.checkerframework.checker.mungo.internal;

import org.checkerframework.checker.mungo.qual.MungoUnknown;
import org.checkerframework.javacutil.AnnotationBuilder;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;

public class MungoUtils {

  // TODO
  public static AnnotationMirror createAnnotation(ProcessingEnvironment env, int groupCount) {
    AnnotationBuilder builder = new AnnotationBuilder(env, MungoUnknown.class);
    if (groupCount > 0) {
      builder.setValue("value", groupCount);
    }
    return builder.build();
  }

}
