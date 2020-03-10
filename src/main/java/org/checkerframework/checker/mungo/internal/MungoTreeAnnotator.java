package org.checkerframework.checker.mungo.internal;

import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;

public class MungoTreeAnnotator extends TreeAnnotator {
  public MungoTreeAnnotator(AnnotatedTypeFactory atypeFactory) {
    super(atypeFactory);
  }
}
