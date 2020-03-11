package org.checkerframework.checker.mungo.annotators

import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.com.google.common.collect.Sets
import org.checkerframework.framework.type.typeannotator.DefaultQualifierForUseTypeAnnotator
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element

class MungoDefaultQualifierForUseTypeAnnotator(private val checker: MungoChecker, typeFactory: MungoAnnotatedTypeFactory) : DefaultQualifierForUseTypeAnnotator(typeFactory) {
  override fun getExplicitAnnos(element: Element): Set<AnnotationMirror> {
    // Extract information from class declaration so that the correct annotations can be applied to instances
    val annotation = checker.getUtils().visitClassSymbol(element)
    val set = super.getExplicitAnnos(element)
    if (annotation != null) {
      val newSet: MutableSet<AnnotationMirror> = Sets.newHashSet(annotation)
      newSet.addAll(set)
      return newSet
    }
    return set
  }

}
