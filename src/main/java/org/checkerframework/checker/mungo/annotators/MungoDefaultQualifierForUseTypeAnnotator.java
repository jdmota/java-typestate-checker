package org.checkerframework.checker.mungo.annotators;

import org.checkerframework.checker.mungo.MungoChecker;
import org.checkerframework.checker.mungo.typecheck.MungoTypeInfo;
import org.checkerframework.com.google.common.collect.Sets;
import org.checkerframework.framework.type.typeannotator.DefaultQualifierForUseTypeAnnotator;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import java.util.Set;

public class MungoDefaultQualifierForUseTypeAnnotator extends DefaultQualifierForUseTypeAnnotator {
  private final MungoChecker checker;

  public MungoDefaultQualifierForUseTypeAnnotator(MungoChecker checker, MungoAnnotatedTypeFactory typeFactory) {
    super(typeFactory);
    this.checker = checker;
  }

  @Override
  protected Set<AnnotationMirror> getExplicitAnnos(Element element) {
    // Extract information from class declaration so that the correct annotations can be applied to instances
    MungoTypeInfo annotation = checker.getUtils().visitClassSymbol(element);
    Set<AnnotationMirror> set = super.getExplicitAnnos(element);
    if (annotation != null) {
      Set<AnnotationMirror> newSet = Sets.newHashSet(annotation);
      newSet.addAll(set);
      return newSet;
    }
    return set;
  }
}
