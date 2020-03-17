package org.checkerframework.checker.mungo.annotators

import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.framework.type.typeannotator.DefaultQualifierForUseTypeAnnotator
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element

class MungoDefaultQualifierForUseTypeAnnotator(private val checker: MungoChecker, typeFactory: MungoAnnotatedTypeFactory) : DefaultQualifierForUseTypeAnnotator(typeFactory) {
  // This is called by Checker when a reference to a class is encountered
  // to providing a variable with the default type information
  override fun getExplicitAnnos(element: Element): Set<AnnotationMirror> {
    // Extract information from class declaration
    val graph = checker.utils.visitClassSymbol(element)
    val set = super.getExplicitAnnos(element)
    if (graph != null) {
      val annotation = MungoUtils.buildAnnotation(checker.processingEnvironment, graph.file)
      val newSet: MutableSet<AnnotationMirror> = mutableSetOf(annotation)
      newSet.addAll(set)
      return newSet
    }
    return set
  }

}
