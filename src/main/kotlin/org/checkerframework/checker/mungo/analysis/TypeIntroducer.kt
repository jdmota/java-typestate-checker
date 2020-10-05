package org.checkerframework.checker.mungo.analysis

import org.checkerframework.checker.mungo.typecheck.*
import org.checkerframework.checker.mungo.utils.ClassUtils
import org.checkerframework.checker.mungo.utils.MungoUtils
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
  // like @MungoNullable, @MungoState, @MungoRequires
  val typeDeclaration: Boolean,
  // If it is a local variable declaration,
  // only take into account @MungoNullable annotation to refine the type
  val localTypeDeclaration: Boolean
)

private fun typeMirrorToMungoType(utils: MungoUtils, annotatedType: AnnotatedTypeMirror, opts: TypeIntroOpts): MungoType {
  val type = annotatedType.underlyingType
  val annotations = annotatedType.annotations
  val isNullable = opts.forceNullable || annotations.any { MungoUtils.nullableAnnotations.contains(AnnotationUtils.annotationName(it)) }

  val mungoType = if (ClassUtils.isJavaLangObject(type)) {
    if (opts.invalidated) {
      MungoUnionType.create(setOf(MungoObjectType.SINGLETON, MungoMovedType.SINGLETON))
    } else {
      MungoObjectType.SINGLETON
    }
  } else {
    val graph = utils.classUtils.visitClassTypeMirror(type)
    if (graph == null) {
      MungoNoProtocolType.SINGLETON
    } else {
      when {
        opts.localTypeDeclaration -> {
          val states = graph.getAllConcreteStates()
          MungoUnionType.create(states.map { MungoStateType.create(graph, it) })
        }
        opts.typeDeclaration -> {
          val stateNames = MungoUtils.getAnnotationValue(annotations.find {
            val name = AnnotationUtils.annotationName(it)
            name == MungoUtils.mungoState || name == MungoUtils.mungoRequires
          })
          val states = if (stateNames == null) {
            graph.getAllConcreteStates()
          } else {
            graph.getAllConcreteStates().filter { stateNames.contains(it.name) }
          }
          MungoUnionType.create(states.map { MungoStateType.create(graph, it) })
        }
        else -> {
          val states = graph.getAllConcreteStates()
          MungoUnionType.create(states.map { MungoStateType.create(graph, it) }.plus(MungoEndedType.SINGLETON).plus(MungoMovedType.SINGLETON))
        }
      }
    }
  }

  return if (isNullable) {
    MungoUnionType.create(listOf(mungoType, MungoNullType.SINGLETON))
  } else {
    MungoUnionType.create(listOf(mungoType))
  }
}

class TypeIntroducer(private val utils: MungoUtils) {

  private val cache = WeakIdentityHashMap<AnnotatedTypeMirror, MungoType>()

  val invalidated = TypeIntroOpts(invalidated = true, forceNullable = false, typeDeclaration = false, localTypeDeclaration = false)
  val invalidatedWithNull = TypeIntroOpts(invalidated = true, forceNullable = true, typeDeclaration = false, localTypeDeclaration = false)
  val declarationOpts = TypeIntroOpts(invalidated = false, forceNullable = false, typeDeclaration = true, localTypeDeclaration = false)
  val localDeclarationOpts = TypeIntroOpts(invalidated = false, forceNullable = false, typeDeclaration = false, localTypeDeclaration = true)

  fun get(type: AnnotatedTypeMirror, opts: TypeIntroOpts): MungoType {
    return when (type) {
      is AnnotatedWildcardType -> get(type.extendsBound, invalidatedWithNull)
      is AnnotatedTypeVariable -> get(type.upperBound, invalidatedWithNull)
      is AnnotatedArrayType -> MungoNoProtocolType.SINGLETON
      is AnnotatedDeclaredType -> typeMirrorToMungoType(utils, type, opts)
      is AnnotatedExecutableType -> MungoUnknownType.SINGLETON
      is AnnotatedPrimitiveType -> MungoPrimitiveType.SINGLETON
      is AnnotatedNoType -> MungoPrimitiveType.SINGLETON // void
      is AnnotatedNullType -> MungoNullType.SINGLETON
      is AnnotatedIntersectionType -> MungoUnknownType.SINGLETON
      is AnnotatedUnionType -> MungoUnknownType.SINGLETON
      else -> throw AssertionError("unexpected ${type.kind}")
    }
  }

  fun apply(type: AnnotatedTypeMirror, opts: TypeIntroOpts): MungoType {
    val curr = cache[type]
    if (curr != null) return curr
    cache[type] = MungoUnknownType.SINGLETON
    val mungoType = when (type) {
      is AnnotatedWildcardType -> apply(type.extendsBound, invalidatedWithNull)
      is AnnotatedTypeVariable -> apply(type.upperBound, invalidatedWithNull)
      is AnnotatedArrayType -> {
        apply(type.componentType, invalidatedWithNull)
        MungoNoProtocolType.SINGLETON
      }
      is AnnotatedDeclaredType -> {
        for (typeVar in type.typeArguments) {
          apply(typeVar, invalidatedWithNull)
        }
        if (type.enclosingType != null) {
          apply(type.enclosingType, invalidatedWithNull)
        }
        typeMirrorToMungoType(utils, type, opts)
      }
      is AnnotatedExecutableType -> {
        // If the return type has annotations or we are sure we have access to the method's code, refine
        if (type.returnType.annotations.any { MungoUtils.isMungoLibAnnotation(it) } || !ElementUtils.isElementFromByteCode(type.element)) {
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
        MungoUnknownType.SINGLETON
      }
      is AnnotatedPrimitiveType -> MungoPrimitiveType.SINGLETON
      is AnnotatedNoType -> MungoPrimitiveType.SINGLETON // void
      is AnnotatedNullType -> MungoNullType.SINGLETON
      is AnnotatedIntersectionType -> MungoUnknownType.SINGLETON
      is AnnotatedUnionType -> MungoUnknownType.SINGLETON
      else -> throw AssertionError("unexpected ${type.kind}")
    }
    cache[type] = mungoType
    return mungoType
  }

}
