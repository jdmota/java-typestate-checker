package org.checkerframework.checker.mungo.internal;

import org.checkerframework.checker.mungo.qual.MungoState;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import java.util.HashSet;
import java.util.Set;

public class MungoUtils {

  public static AnnotationMirror createStateAnnotation(ProcessingEnvironment env, Set<String> states) {
    return createStateAnnotation(env, states.toArray(new String[] {}));
  }

  public static AnnotationMirror createStateAnnotation(ProcessingEnvironment env, String[] states) {
    AnnotationBuilder builder = new AnnotationBuilder(env, MungoState.class);
    builder.setValue("value", states);
    return builder.build();
  }

  // "anno" is @MungoState
  public static Set<String> getStatesFromAnno(AnnotationMirror anno) {
    return new HashSet<>(AnnotationUtils.getElementValueArray(anno, "value", String.class, false));
  }

}
