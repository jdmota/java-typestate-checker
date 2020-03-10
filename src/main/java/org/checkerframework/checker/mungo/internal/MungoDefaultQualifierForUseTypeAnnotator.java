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
    AnnotationMirror annotation = utils.visitClassSymbol(element);
    Set<AnnotationMirror> set = super.getExplicitAnnos(element);
    System.out.println(element + " " + set + " " + annotation);
    if (annotation != null) {
      Set<AnnotationMirror> newSet = Sets.newHashSet(annotation);
      newSet.addAll(set);
      return newSet;
    }
    return set;
  }
}
