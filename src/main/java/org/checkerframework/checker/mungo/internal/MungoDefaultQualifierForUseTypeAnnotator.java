package org.checkerframework.checker.mungo.internal;

import org.checkerframework.checker.mungo.MungoAnnotatedTypeFactory;
import org.checkerframework.com.google.common.collect.Sets;
import org.checkerframework.framework.type.typeannotator.DefaultQualifierForUseTypeAnnotator;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import java.util.Set;

public class MungoDefaultQualifierForUseTypeAnnotator extends DefaultQualifierForUseTypeAnnotator {
  private final MungoUtils utils;

  public MungoDefaultQualifierForUseTypeAnnotator(MungoAnnotatedTypeFactory typeFactory) {
    super(typeFactory);
    this.utils = typeFactory.utils;
  }

  @Override
  protected Set<AnnotationMirror> getExplicitAnnos(Element element) {
    // Extract information from class declaration so that the correct annotations can be applied to instances
    AnnotationMirror annotation = utils.visitClassSymbol(element);
    Set<AnnotationMirror> set = super.getExplicitAnnos(element);
    if (annotation != null) {
      Set<AnnotationMirror> newSet = Sets.newHashSet(annotation);
      newSet.addAll(set);
      return newSet;
    }
    return set;
  }
}
