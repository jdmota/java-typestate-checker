package jatyc.core

import com.sun.source.tree.VariableTree
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.code.Type
import jatyc.JavaTypestateChecker
import jatyc.utils.JTCUtils
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.framework.type.AnnotatedTypeMirror.*
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.javacutil.ElementUtils
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.type.*

data class TypeIntroOpts(
  // Keep it as shared
  val forceShared: Boolean = false,
  // If there is a chance that it is nullable even without annotations
  // E.g. generic parameters, parameters and return values of methods which code we cannot analyze
  val forceNullable: Boolean = false,
  // Annotation name to look for
  val annotation: String? // JTCUtils.jtcRequiresAnno OR JTCUtils.jtcEnsuresAnno
)

class TypeIntroducer(private val checker: JavaTypestateChecker, private val hierarchy: JavaTypesHierarchy) {
  private val utils get() = checker.utils
  val nonNullableShared = TypeIntroOpts(forceShared = true, forceNullable = false, annotation = null)
  val nullableShared = TypeIntroOpts(forceShared = true, forceNullable = true, annotation = null)

  private fun processArrayType(type: TypeMirror, annotations: Set<AnnotationMirror>, opts: TypeIntroOpts): JTCType {
    val javaType = hierarchy.get(type)
    val isNullable = opts.forceNullable || annotations.any { JTCUtils.nullableAnnotations.contains(AnnotationUtils.annotationName(it)) }
    return if (isNullable) JTCSharedType(javaType).union(JTCNullType.SINGLETON) else JTCSharedType(javaType)
  }

  private fun processDeclaredType(type: TypeMirror, annotations: Set<AnnotationMirror>, opts: TypeIntroOpts): JTCType {
    val javaType = hierarchy.get(type)
    val isNullable = opts.forceNullable || annotations.any { JTCUtils.nullableAnnotations.contains(AnnotationUtils.annotationName(it)) }

    val jtcType =
      if (opts.forceShared) {
        JTCSharedType(javaType)
      } else {
        val graph = utils.classUtils.getGraph(type)
        if (graph == null) {
          JTCSharedType(javaType)
        } else {
          val stateNames = JTCUtils.getAnnotationValue(annotations.find {
            AnnotationUtils.annotationName(it) == opts.annotation
          })
          if (stateNames == null) {
            JTCSharedType(javaType)
          } else {
            val states = graph.getAllConcreteStates().filter { stateNames.contains(it.name) }
            JTCType.createUnion(states.map { JTCStateType(javaType, graph, it) })
          }
        }
      }

    return jtcType.toMaybeNullable(isNullable)
  }

  fun get(type: AnnotatedTypeMirror, opts: TypeIntroOpts): JTCType {
    return when (type) {
      is AnnotatedWildcardType -> JTCSharedType(hierarchy.get(type.underlyingType)).union(JTCNullType.SINGLETON)
      is AnnotatedTypeVariable -> JTCSharedType(hierarchy.get(type.underlyingType)).union(JTCNullType.SINGLETON)
      is AnnotatedArrayType -> processArrayType(type.underlyingType, type.annotations, opts)
      is AnnotatedDeclaredType -> processDeclaredType(type.underlyingType, type.annotations, opts)
      is AnnotatedExecutableType -> JTCUnknownType.SINGLETON
      is AnnotatedPrimitiveType -> hierarchy.getPrimitive(type.underlyingType as Type.JCPrimitiveType)
      is AnnotatedNoType -> JTCNullType.SINGLETON // void
      is AnnotatedNullType -> JTCNullType.SINGLETON
      is AnnotatedIntersectionType -> JTCUnknownType.SINGLETON
      is AnnotatedUnionType -> JTCUnknownType.SINGLETON
      else -> throw AssertionError("unexpected ${type.kind}")
    }
  }

  fun getJavaType(type: TypeMirror) = hierarchy.get(type)

  fun getInitialType(type: TypeMirror): JTCType {
    val javaType = hierarchy.get(type)
    val graph = javaType.getGraph()
    return if (graph == null) {
      JTCSharedType(javaType)
      // JTCNoProtocolType(javaType, true)
    } else {
      JTCStateType(javaType, graph, graph.getInitialState())
    }
  }

  fun getThisType(type: TypeMirror, isAnytime: Boolean, isConstructor: Boolean): JTCType {
    val javaType = hierarchy.get(type)
    return if (isAnytime) {
      JTCSharedType(javaType)
    } else {
      val graph = javaType.getGraph()
      if (graph == null) {
        if (isConstructor) {
          JTCSharedType(javaType)
          // JTCNoProtocolType(javaType, false)
        } else {
          JTCSharedType(javaType)
        }
      } else {
        JTCLinearType(javaType, graph)
      }
    }
  }

  fun getUpperBound(type: TypeMirror, isNullable: Boolean = true, isActualType: Boolean = false): JTCType {
    return when (type) {
      is WildcardType,
      is TypeVariable,
      is ArrayType -> JTCSharedType(hierarchy.get(type)).toMaybeNullable(isNullable)
      is DeclaredType -> {
        val javaType = hierarchy.get(type)
        val graph = javaType.getGraph()
        if (graph == null) {
          JTCSharedType(javaType)/*.union(JTCNoProtocolType(javaType, isActualType))*/.toMaybeNullable(isNullable)
        } else {
          JTCSharedType(javaType).union(JTCLinearType(javaType, graph)).toMaybeNullable(isNullable)
        }
      }
      is ExecutableType -> JTCUnknownType.SINGLETON
      is PrimitiveType -> hierarchy.getPrimitive(type as Type.JCPrimitiveType)
      is NoType -> JTCNullType.SINGLETON // void
      is NullType -> JTCNullType.SINGLETON
      is IntersectionType -> JTCUnknownType.SINGLETON
      is UnionType -> JTCUnknownType.SINGLETON
      else -> throw AssertionError("unexpected ${type.kind}")
    }
  }

  fun getCastType(type: TypeMirror): JTCType {
    return getUpperBound(type, isNullable = true, isActualType = false)
  }

  fun getArrayComponentType(type: TypeMirror): JTCType {
    return when (type) {
      is WildcardType,
      is TypeVariable,
      is ArrayType -> JTCSharedType(hierarchy.get(type)).toMaybeNullable(true)
      is DeclaredType -> {
        val javaType = hierarchy.get(type)
        JTCSharedType(javaType).toMaybeNullable(true)
      }
      is ExecutableType -> JTCUnknownType.SINGLETON
      is PrimitiveType -> hierarchy.getPrimitive(type as Type.JCPrimitiveType)
      is NoType -> JTCNullType.SINGLETON // void
      is NullType -> JTCNullType.SINGLETON
      is IntersectionType -> JTCUnknownType.SINGLETON
      is UnionType -> JTCUnknownType.SINGLETON
      else -> throw AssertionError("unexpected ${type.kind}")
    }
  }

  fun getFieldUpperBound(tree: VariableTree, type: AnnotatedTypeMirror): JTCType {
    val typeMirror = type.underlyingType
    val isNullable = type.annotations.any { JTCUtils.nullableAnnotations.contains(AnnotationUtils.annotationName(it)) }
    return when (typeMirror) {
      is WildcardType,
      is TypeVariable,
      is ArrayType -> JTCSharedType(hierarchy.get(typeMirror)).toMaybeNullable(isNullable)
      is DeclaredType -> {
        val javaType = hierarchy.get(typeMirror)
        val graph = javaType.getGraph()
        if (graph == null) {
          JTCSharedType(javaType)/*.union(JTCNoProtocolType(javaType, false))*/.toMaybeNullable(isNullable)
        } else {
          JTCSharedType(javaType).union(JTCLinearType(javaType, graph)).toMaybeNullable(isNullable)
        }
      }
      is ExecutableType -> JTCUnknownType.SINGLETON
      is PrimitiveType -> hierarchy.getPrimitive(typeMirror as Type.JCPrimitiveType)
      is NoType -> JTCNullType.SINGLETON // void
      is NullType -> JTCNullType.SINGLETON
      is IntersectionType -> JTCUnknownType.SINGLETON
      is UnionType -> JTCUnknownType.SINGLETON
      else -> throw AssertionError("unexpected ${typeMirror.kind}")
    }
  }

  fun getEnumFieldType(typeMirror: TypeMirror, field: String): JTCType? {
    val type = (typeMirror as Type).tsym
    if (type is Symbol.ClassSymbol && type.isEnum) {
      val symbol = type.members().symbols.find {
        it is Symbol.VarSymbol && it.simpleName.toString() == field && ElementUtils.isStatic(it)
      }
      if (symbol != null) {
        return getUpperBound(symbol.asType(), isNullable = false, isActualType = true).toShared()
      }
    }
    return null
  }

  private class JDKOpts(val isNullable: Boolean, val isActualType: Boolean)

  private val jdkStaticFields = mutableMapOf<String, Map<String, JDKOpts>>()

  init {
    // TODO is it possible for some of these to have a protocol?
    val nonNullActual = JDKOpts(isNullable = false, isActualType = true)
    jdkStaticFields["java.lang.System"] = listOf("err", "in", "out").associateWith { nonNullActual }
  }

  fun getJDKStaticFieldType(typeMirror: TypeMirror, field: String): JTCType? {
    val type = (typeMirror as Type).tsym
    if (type is Symbol.ClassSymbol) {
      val classQualifiedName = type.qualifiedName.toString()
      val opts = jdkStaticFields[classQualifiedName]?.get(field)
      val symbol = type.members().symbols.find {
        it is Symbol.VarSymbol && it.simpleName.toString() == field && ElementUtils.isStatic(it)
      }
      if (opts != null && symbol != null) {
        return getUpperBound(symbol.asType(), isNullable = opts.isNullable, isActualType = opts.isActualType).toShared()
      }
    }
    return null
  }

  private fun getExecutableKey(type: AnnotatedExecutableType): String {
    val element = type.element
    val dot = if (ElementUtils.isStatic(element)) "." else "#"
    return "${element.enclosingElement}$dot${element.simpleName}"
  }

  private val jdkNonNullReturns = mutableSetOf<String>()

  init {
    jdkNonNullReturns.add("java.util.Arrays.asList")
    jdkNonNullReturns.add("java.net.Socket#getInputStream")
    jdkNonNullReturns.add("java.net.Socket#getOutputStream")
    jdkNonNullReturns.add("java.lang.String#toUpperCase")
    jdkNonNullReturns.add("java.lang.String#toLowerCase")
    jdkNonNullReturns.add("java.lang.String#toString")
    jdkNonNullReturns.add("java.lang.StringBuilder#toString")
    jdkNonNullReturns.add("java.util.Scanner#next")
    jdkNonNullReturns.add("java.util.Scanner#nextLine")
    jdkNonNullReturns.add("java.util.ArrayList#iterator")
    jdkNonNullReturns.add("java.util.List#iterator")
  }

  fun returnsNonNull(type: AnnotatedExecutableType): Boolean {
    return jdkNonNullReturns.contains(getExecutableKey(type))
  }

  private val jdkAcceptsNull = mutableSetOf<String>()

  init {
    jdkAcceptsNull.add("java.io.PrintStream#print")
    jdkAcceptsNull.add("java.io.PrintStream#println")
  }

  fun acceptsNull(type: AnnotatedExecutableType): Boolean {
    return jdkAcceptsNull.contains(getExecutableKey(type))
  }

  private val jdkTerminates = mutableSetOf<String>()

  init {
    jdkTerminates.add("java.lang.System.exit")
  }

  fun terminates(type: AnnotatedExecutableType): Boolean {
    return jdkTerminates.contains(getExecutableKey(type))
  }
}
