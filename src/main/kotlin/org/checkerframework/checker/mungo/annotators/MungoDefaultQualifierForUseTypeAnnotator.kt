package org.checkerframework.checker.mungo.annotators

import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.typecheck.MungoNoProtocolType
import org.checkerframework.checker.mungo.typecheck.MungoStateType
import org.checkerframework.checker.mungo.typecheck.MungoUnionType
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
    val set = super.getExplicitAnnos(element).toMutableSet()
    if (graph == null) {
      set.add(MungoNoProtocolType.SINGLETON.buildAnnotation(checker.processingEnvironment))
    } else {
      set.add(createTypeWithAllStates(graph).buildAnnotation(checker.processingEnvironment))
    }
    return set
  }

  override fun visitDeclared(type: AnnotatedTypeMirror.AnnotatedDeclaredType, aVoid: Void?): Void? {
    val ret = super.visitDeclared(type, aVoid)
    val element = type.underlyingType.asElement()
    val stateAnno = type.underlyingType.annotationMirrors.find { AnnotationUtils.areSameByName(it, MungoUtils.mungoStateName) }
    if (stateAnno != null) {
      val graph = checker.utils.visitClassSymbol(element)
      if (graph != null) {
        val stateNames = AnnotationUtils.getElementValueArray(stateAnno, "value", String::class.java, false)
        if (stateNames != null) {
          val states = graph.getAllConcreteStates().filter { stateNames.contains(it.name) }
          type.replaceAnnotation(MungoUnionType.create(states.map { MungoStateType.create(graph, it) }).buildAnnotation(checker.processingEnvironment))
          // FIXME error location
          checker.utils.checkStates(graph.file, stateNames, element)
        }
      } else {
        // FIXME error location
        checker.utils.err("@MungoState has no meaning since this type has no protocol", element)
      }
    }
    return ret
  }

  override fun visitArray(type: AnnotatedTypeMirror.AnnotatedArrayType, p: Void?): Void? {
    val ret = super.visitArray(type, p)
    type.replaceAnnotation(MungoNoProtocolType.SINGLETON.buildAnnotation(checker.processingEnvironment))
    return ret
  }

  override fun visitPrimitive(type: AnnotatedTypeMirror.AnnotatedPrimitiveType, p: Void?): Void? {
    val ret = super.visitPrimitive(type, p)
    type.replaceAnnotation(MungoNoProtocolType.SINGLETON.buildAnnotation(checker.processingEnvironment))
    return ret
  }

  override fun visitNoType(type: AnnotatedTypeMirror.AnnotatedNoType, p: Void?): Void? {
    val ret = super.visitNoType(type, p)
    type.replaceAnnotation(MungoNoProtocolType.SINGLETON.buildAnnotation(checker.processingEnvironment))
    return ret
  }
}
