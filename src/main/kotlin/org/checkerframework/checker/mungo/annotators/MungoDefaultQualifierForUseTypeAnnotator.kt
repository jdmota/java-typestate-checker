package org.checkerframework.checker.mungo.annotators

import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.typecheck.MungoConcreteType
import org.checkerframework.checker.mungo.typecheck.createTypeWithAllStates
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.framework.type.typeannotator.DefaultQualifierForUseTypeAnnotator
import org.checkerframework.javacutil.AnnotationUtils
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
      val annotation = createTypeWithAllStates(graph).buildAnnotation(checker.processingEnvironment)
      val newSet: MutableSet<AnnotationMirror> = mutableSetOf(annotation)
      newSet.addAll(set)
      return newSet
    }
    return set
  }

  override fun visitDeclared(type: AnnotatedTypeMirror.AnnotatedDeclaredType, aVoid: Void?): Void? {
    val ret = super.visitDeclared(type, aVoid)
    val stateAnno = type.underlyingType.annotationMirrors.find { AnnotationUtils.areSameByName(it, MungoUtils.mungoStateName) }
    if (stateAnno != null) {
      val info = MungoUtils.mungoTypeFromAnnotations(type.annotations)
      if (info is MungoConcreteType) {
        val stateNames = AnnotationUtils.getElementValueArray(stateAnno, "value", String::class.java, false)
        if (stateNames != null) {
          val states = info.graph.getAllConcreteStates().filter { stateNames.contains(it.name) }.toSet()
          type.replaceAnnotation(MungoConcreteType(info.graph, states).buildAnnotation(checker.processingEnvironment))
          // FIXME error location
          checker.utils.checkStates(info.graph.file, stateNames, type.underlyingType.asElement())
        }
      } else {
        // FIXME error location
        checker.utils.err("@MungoState has no meaning since this type has no protocol", type.underlyingType.asElement())
      }
    }
    return ret
  }
}
