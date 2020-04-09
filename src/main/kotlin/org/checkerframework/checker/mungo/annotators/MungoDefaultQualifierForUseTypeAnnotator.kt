package org.checkerframework.checker.mungo.annotators

import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.typecheck.*
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.framework.type.typeannotator.DefaultQualifierForUseTypeAnnotator
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element

class MungoDefaultQualifierForUseTypeAnnotator(private val checker: MungoChecker, private val factory: MungoAnnotatedTypeFactory) : DefaultQualifierForUseTypeAnnotator(factory) {
  // This is called by Checker when a reference to a class is encountered
  // to provide a variable with the default type information
  override fun getExplicitAnnos(element: Element): Set<AnnotationMirror> {
    // Extract information from class declaration
    val graph = checker.utils.classUtils.visitClassSymbol(element)
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
    factory.visitMungoAnnotations(type, null)
    return ret
  }

  override fun visitNull(type: AnnotatedTypeMirror.AnnotatedNullType, p: Void?): Void? {
    val ret = super.visitNull(type, p)
    type.replaceAnnotation(MungoNullType.SINGLETON.buildAnnotation(checker.processingEnvironment))
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
