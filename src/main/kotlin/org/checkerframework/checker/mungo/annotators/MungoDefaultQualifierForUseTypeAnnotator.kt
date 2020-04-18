package org.checkerframework.checker.mungo.annotators

import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.typecheck.*
import org.checkerframework.checker.mungo.utils.ClassUtils
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.framework.type.typeannotator.DefaultQualifierForUseTypeAnnotator
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element

class MungoDefaultQualifierForUseTypeAnnotator(private val checker: MungoChecker, private val factory: MungoAnnotatedTypeFactory) : DefaultQualifierForUseTypeAnnotator(factory) {

  override fun visitDeclared(type: AnnotatedTypeMirror.AnnotatedDeclaredType, aVoid: Void?): Void? {
    val ret = super.visitDeclared(type, aVoid)
    factory.visitDeclaredType(type, null)
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
    type.replaceAnnotation(MungoPrimitiveType.SINGLETON.buildAnnotation(checker.processingEnvironment))
    return ret
  }

  override fun visitNoType(type: AnnotatedTypeMirror.AnnotatedNoType, p: Void?): Void? {
    val ret = super.visitNoType(type, p)
    type.replaceAnnotation(MungoNoProtocolType.SINGLETON.buildAnnotation(checker.processingEnvironment))
    return ret
  }

  override fun visitTypeVariable(type: AnnotatedTypeMirror.AnnotatedTypeVariable, p: Void?): Void? {
    val ret = super.visitTypeVariable(type, p)
    // Null type should not be the lower bound of type variables in generics
    // Avoiding type.argument.type.incompatible errors
    if (type.lowerBound is AnnotatedTypeMirror.AnnotatedNullType) {
      type.lowerBound.replaceAnnotation(MungoBottomType.SINGLETON.buildAnnotation(checker.processingEnvironment))
    }
    return ret
  }
}
