package org.checkerframework.checker.jtc.analysis

import org.checkerframework.checker.jtc.typecheck.*
import org.checkerframework.checker.jtc.utils.ClassUtils
import org.checkerframework.checker.jtc.utils.JTCUtils
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.framework.type.AnnotatedTypeMirror.*
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.javacutil.ElementUtils
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap

data class TypeIntroOpts(
  // If it needs to consider all possible types
  val invalidated: Boolean,
  // If there is a chance that it is nullable even without annotations
  // E.g. generic parameters, parameters and return values of methods which code we cannot analyze
  val forceNullable: Boolean,
  // If it is a type declaration,
  // take into account annotations to refine the type,
  // like @Nullable, @State, @Requires
  val typeDeclaration: Boolean,
  // If it is a local variable declaration,
  // only take into account @Nullable annotation to refine the type
  val localTypeDeclaration: Boolean
)

private fun typeMirrorToJTCType(utils: JTCUtils, annotatedType: AnnotatedTypeMirror, opts: TypeIntroOpts): JTCType {
  val type = annotatedType.underlyingType
  val annotations = annotatedType.annotations
  val isNullable = opts.forceNullable || annotations.any { JTCUtils.nullableAnnotations.contains(AnnotationUtils.annotationName(it)) }

  val jtcType = if (ClassUtils.isJavaLangObject(type)) {
    if (opts.invalidated) {
      JTCUnionType.create(setOf(JTCObjectType.SINGLETON, JTCMovedType.SINGLETON))
    } else {
      JTCObjectType.SINGLETON
    }
  } else {
    val graph = utils.classUtils.visitClassTypeMirror(type)
    if (graph == null) {
      JTCNoProtocolType.SINGLETON
    } else {
      when {
        opts.localTypeDeclaration -> {
          val states = graph.getAllConcreteStates()
          JTCUnionType.create(states.map { JTCStateType.create(graph, it) }.plus(JTCEndedType.SINGLETON))
        }
        opts.typeDeclaration -> {
          val stateNames = JTCUtils.getAnnotationValue(annotations.find {
            val name = AnnotationUtils.annotationName(it)
            name == JTCUtils.jtcStateAnno || name == JTCUtils.jtcRequiresAnno
          })
          val states = if (stateNames == null) {
            graph.getAllConcreteStates()
          } else {
            graph.getAllConcreteStates().filter { stateNames.contains(it.name) }
          }
          JTCUnionType.create(states.map { JTCStateType.create(graph, it) })
        }
        else -> {
          val states = graph.getAllConcreteStates()
          JTCUnionType.create(states.map { JTCStateType.create(graph, it) }.plus(JTCEndedType.SINGLETON).plus(JTCMovedType.SINGLETON))
        }
      }
    }
  }

  return if (isNullable) {
    JTCUnionType.create(listOf(jtcType, JTCNullType.SINGLETON))
  } else {
    JTCUnionType.create(listOf(jtcType))
  }
}

class TypeIntroducer(private val utils: JTCUtils) {

  private val cache = WeakIdentityHashMap<AnnotatedTypeMirror, JTCType>()

  val invalidated = TypeIntroOpts(invalidated = true, forceNullable = false, typeDeclaration = false, localTypeDeclaration = false)
  val invalidatedWithNull = TypeIntroOpts(invalidated = true, forceNullable = true, typeDeclaration = false, localTypeDeclaration = false)
  val declarationOpts = TypeIntroOpts(invalidated = false, forceNullable = false, typeDeclaration = true, localTypeDeclaration = false)
  val localDeclarationOpts = TypeIntroOpts(invalidated = false, forceNullable = false, typeDeclaration = false, localTypeDeclaration = true)

  fun get(type: AnnotatedTypeMirror, opts: TypeIntroOpts): JTCType {
    return when (type) {
      is AnnotatedWildcardType -> get(type.extendsBound, invalidatedWithNull)
      is AnnotatedTypeVariable -> get(type.upperBound, invalidatedWithNull)
      is AnnotatedArrayType -> JTCNoProtocolType.SINGLETON
      is AnnotatedDeclaredType -> typeMirrorToJTCType(utils, type, opts)
      is AnnotatedExecutableType -> JTCUnknownType.SINGLETON
      is AnnotatedPrimitiveType -> JTCPrimitiveType.SINGLETON
      is AnnotatedNoType -> JTCPrimitiveType.SINGLETON // void
      is AnnotatedNullType -> JTCNullType.SINGLETON
      is AnnotatedIntersectionType -> JTCUnknownType.SINGLETON
      is AnnotatedUnionType -> JTCUnknownType.SINGLETON
      else -> throw AssertionError("unexpected ${type.kind}")
    }
  }

  fun apply(type: AnnotatedTypeMirror, opts: TypeIntroOpts): JTCType {
    val curr = cache[type]
    if (curr != null) return curr
    cache[type] = JTCUnknownType.SINGLETON
    val jtcType = when (type) {
      is AnnotatedWildcardType -> apply(type.extendsBound, invalidatedWithNull)
      is AnnotatedTypeVariable -> apply(type.upperBound, invalidatedWithNull)
      is AnnotatedArrayType -> {
        apply(type.componentType, invalidatedWithNull)
        JTCNoProtocolType.SINGLETON
      }
      is AnnotatedDeclaredType -> {
        for (typeVar in type.typeArguments) {
          apply(typeVar, invalidatedWithNull)
        }
        if (type.enclosingType != null) {
          apply(type.enclosingType, invalidatedWithNull)
        }
        typeMirrorToJTCType(utils, type, opts)
      }
      is AnnotatedExecutableType -> {
        // If the return type has annotations or we are sure we have access to the method's code, refine
        if (type.returnType.annotations.any { JTCUtils.isLibAnnotation(it) } || !ElementUtils.isElementFromByteCode(type.element)) {
          apply(type.returnType, declarationOpts)
        } else {
          apply(type.returnType, invalidatedWithNull)
        }

        if (type.receiverType != null) {
          apply(type.receiverType!!, invalidatedWithNull)
        }
        for (paramType in type.parameterTypes) {
          apply(paramType, declarationOpts)
        }
        for (thrownType in type.thrownTypes) {
          apply(thrownType, invalidatedWithNull)
        }
        for (typeVar in type.typeVariables) {
          apply(typeVar, invalidatedWithNull)
        }
        JTCUnknownType.SINGLETON
      }
      is AnnotatedPrimitiveType -> JTCPrimitiveType.SINGLETON
      is AnnotatedNoType -> JTCPrimitiveType.SINGLETON // void
      is AnnotatedNullType -> JTCNullType.SINGLETON
      is AnnotatedIntersectionType -> JTCUnknownType.SINGLETON
      is AnnotatedUnionType -> JTCUnknownType.SINGLETON
      else -> throw AssertionError("unexpected ${type.kind}")
    }
    cache[type] = jtcType
    return jtcType
  }

}
