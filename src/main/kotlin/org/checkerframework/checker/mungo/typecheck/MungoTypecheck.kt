package org.checkerframework.checker.mungo.typecheck

import com.sun.source.tree.MemberSelectTree
import com.sun.source.tree.MethodInvocationTree
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.code.Type
import org.checkerframework.checker.mungo.typestate.graph.DecisionState
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.checker.mungo.typestate.graph.State
import org.checkerframework.checker.mungo.utils.ClassUtils
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.javacutil.TreeUtils
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.type.TypeKind
import javax.lang.model.type.TypeMirror

object MungoTypecheck {
  fun available(utils: MungoUtils, graph: Graph, method: Symbol.MethodSymbol): List<MungoType> {
    val env = graph.getEnv()
    return graph.getAllConcreteStates().filter { state ->
      // TODO with generics support, replace sameErasedMethod for sameMethod
      state.transitions.entries.any { utils.methodUtils.sameErasedMethod(env, method, it.key) }
    }.map { MungoStateType.create(graph, it) }
  }

  fun check(
    utils: MungoUtils,
    info: MungoType,
    node: MethodInvocationTree,
    method: Symbol.MethodSymbol
  ): Boolean {
    val error = when (info) {
      is MungoUnknownType -> createErrorMsg(node, isUnknown = true)
      is MungoObjectType -> createErrorMsg(node, isObject = true)
      is MungoBottomType -> null // Allow operations on the BottomType to avoid propagating errors
      is MungoNoProtocolType -> null // Any call allowed on NoProtocol
      is MungoPrimitiveType -> null // Calls on primitive values are not possible, so just ignore
      is MungoNullType -> createErrorMsg(node, isNull = true)
      is MungoEndedType -> createErrorMsg(node, isEnded = true)
      is MungoMovedType -> createErrorMsg(node, isMoved = true)
      is MungoStateType -> {
        val env = info.graph.getEnv()
        // TODO with generics support, replace sameErasedMethod for sameMethod
        if (info.state.transitions.entries.any { utils.methodUtils.sameErasedMethod(env, method, it.key) }) {
          null
        } else {
          createErrorMsg(node, unexpectedStates = listOf(info.state.name), currentStates = listOf(info.state.name))
        }
      }
      is MungoUnionType -> {
        val currentStates = mutableListOf<String>()
        val unexpectedStates = mutableListOf<String>()
        var isObject = false
        var isNull = false
        var isEnded = false
        var isMoved = false
        for (type in info.types) {
          when (type) {
            is MungoObjectType -> isObject = true
            is MungoNullType -> isNull = true
            is MungoEndedType -> isEnded = true
            is MungoMovedType -> isMoved = true
            is MungoPrimitiveType -> {
              // Calls on primitive values are not possible, so just ignore
            }
            is MungoNoProtocolType -> {
              // Any call allowed on NoProtocol
            }
            is MungoStateType -> {
              currentStates.add(type.state.name)
              val env = type.graph.getEnv()
              if (!type.state.transitions.entries.any { utils.methodUtils.sameMethod(env, method, it.key) }) {
                unexpectedStates.add(type.state.name)
              }
            }
            else -> throw AssertionError("union has ${type.javaClass}")
          }
        }
        if (isNull || isEnded || isMoved || unexpectedStates.size > 0) {
          createErrorMsg(node, isObject = isObject, isNull = isNull, isEnded = isEnded, isMoved = isMoved, unexpectedStates = unexpectedStates, currentStates = currentStates)
        } else {
          null
        }
      }
    }
    return if (error == null) {
      true
    } else {
      utils.err(error, node)
      false
    }
  }

  private fun createErrorMsg(
    node: MethodInvocationTree,
    isUnknown: Boolean = false,
    isObject: Boolean = false,
    isNull: Boolean = false,
    isEnded: Boolean = false,
    isMoved: Boolean = false,
    unexpectedStates: List<String> = listOf(),
    currentStates: List<String> = listOf()
  ): String {
    val m = TreeUtils.methodName(node)
    val items = mutableListOf<String>()
    if (isUnknown) items.add("on unknown")
    if (isObject) items.add("on object")
    if (isNull) items.add("on null")
    if (isEnded) items.add("on ended protocol")
    if (isMoved) items.add("on moved value")
    if (unexpectedStates.isNotEmpty()) items.add("on state${if (unexpectedStates.size > 1) "s" else ""} ${unexpectedStates.joinToString(", ")} (got: ${currentStates.joinToString(", ")})")
    return "Cannot call $m ${items.joinToString(", ")}"
  }

  fun checkFieldAccess(
    utils: MungoUtils,
    info: MungoType,
    node: MemberSelectTree
  ): Boolean {
    val error = when (info) {
      is MungoUnknownType -> createErrorMsg(node, isUnknown = true)
      is MungoObjectType -> createErrorMsg(node, isObject = true)
      is MungoBottomType -> null // Allow operations on the BottomType to avoid propagating errors
      is MungoNoProtocolType -> null // Any access allowed on NoProtocol
      is MungoPrimitiveType -> null // Accesses on primitive values are not possible, so just ignore
      is MungoNullType -> createErrorMsg(node, isNull = true)
      is MungoEndedType -> createErrorMsg(node, isEnded = true)
      is MungoMovedType -> createErrorMsg(node, isMoved = true)
      is MungoStateType -> null
      is MungoUnionType -> {
        var isObject = false
        var isNull = false
        var isEnded = false
        var isMoved = false
        for (type in info.types) {
          when (type) {
            is MungoObjectType -> isObject = true
            is MungoNullType -> isNull = true
            is MungoEndedType -> isEnded = true
            is MungoMovedType -> isMoved = true
            is MungoPrimitiveType -> {
              // Accesses on primitive values are not possible, so just ignore
            }
            is MungoNoProtocolType -> {
              // Any access allowed on NoProtocol
            }
            is MungoStateType -> {
              // Allowed
            }
            else -> throw AssertionError("union has ${type.javaClass}")
          }
        }
        if (isNull || isEnded || isMoved) {
          createErrorMsg(node, isObject = isObject, isNull = isNull, isEnded = isEnded, isMoved = isMoved)
        } else {
          null
        }
      }
    }
    return if (error == null) {
      true
    } else {
      utils.err(error, node)
      false
    }
  }

  private fun createErrorMsg(
    node: MemberSelectTree,
    isUnknown: Boolean = false,
    isObject: Boolean = false,
    isNull: Boolean = false,
    isEnded: Boolean = false,
    isMoved: Boolean = false
  ): String {
    val fieldName = node.identifier.toString()
    val items = mutableListOf<String>()
    if (isUnknown) items.add("on unknown")
    if (isObject) items.add("on object")
    if (isNull) items.add("on null")
    if (isEnded) items.add("on ended protocol")
    if (isMoved) items.add("on moved value")
    return "Cannot access $fieldName ${items.joinToString(", ")}"
  }

  fun refine(utils: MungoUtils, tree: TreePath, type: MungoType, method: Symbol.MethodSymbol, predicate: (String) -> Boolean): MungoType {
    return when (type) {
      // Unknown stays Unknown
      is MungoUnknownType -> MungoUnknownType.SINGLETON
      // Object stays Object
      is MungoObjectType -> MungoObjectType.SINGLETON
      // Bottom stays bottom
      is MungoBottomType -> MungoBottomType.SINGLETON
      // Calling a method on null would produce an exception, so the method call has bottom type
      is MungoNullType -> MungoBottomType.SINGLETON
      // Since the "end" has no transitions, we refine to an empty set of states
      is MungoEndedType -> MungoBottomType.SINGLETON
      // Refine to bottom to avoid propagating errors
      is MungoMovedType -> MungoBottomType.SINGLETON
      // Calls on primitive values not possible anyway
      is MungoPrimitiveType -> MungoBottomType.SINGLETON
      // Objects with no protocol, stay like that
      is MungoNoProtocolType -> MungoNoProtocolType.SINGLETON
      // Refine...
      is MungoUnionType -> MungoUnionType.create(type.types.map { refine(utils, tree, it, method, predicate) })
      is MungoStateType -> MungoUnionType.create(refine(utils, type, method, predicate))
    }
  }

  private fun refine(utils: MungoUtils, type: MungoStateType, method: Symbol.MethodSymbol, predicate: (String) -> Boolean): List<MungoType> {
    val env = type.graph.getEnv()
    // Given a current state, produce a set of possible destination states
    val dest = type.state.transitions.entries.find { utils.methodUtils.sameMethod(env, method, it.key) }?.value
    return when (dest) {
      is State -> listOf(MungoStateType.create(type.graph, dest))
      is DecisionState -> dest.transitions.entries.filter { predicate(it.key.label) }.map { MungoStateType.create(type.graph, it.value) }
      // The method call is not allowed in this state,
      // so return an empty list (imagine this as the bottom type).
      // The union of some type T with the bottom type, is T,
      // which is fine. The MungoVisitor will later ensure a call is safe
      // by checking that the method is available in all states.
      else -> listOf()
    }
  }

  fun refineToNonNull(type: MungoType): MungoType {
    return when (type) {
      // Refine...
      is MungoNullType -> MungoBottomType.SINGLETON
      is MungoUnionType -> MungoUnionType.create(type.types.map { refineToNonNull(it) })
      // Others...
      else -> type
    }
  }

  fun refineToNull(type: MungoType): MungoType {
    return if (MungoNullType.SINGLETON.isSubtype(type)) MungoNullType.SINGLETON else MungoBottomType.SINGLETON
  }

  fun canDrop(type: MungoType): Boolean {
    return type.isSubtype(acceptedFinalTypes) || when (type) {
      is MungoUnionType -> type.types.any { type is MungoStateType && type.state.isDroppable }
      is MungoStateType -> type.state.isDroppable
      else -> false
    }
  }

  fun objectCreation(utils: MungoUtils, type: TypeMirror): MungoType {
    return if (ClassUtils.isJavaLangObject(type)) {
      MungoObjectType.SINGLETON
    } else {
      val graph = utils.classUtils.visitClassTypeMirror(type)
      if (graph == null) {
        MungoNoProtocolType.SINGLETON
      } else {
        MungoStateType.create(graph, graph.getInitialState())
      }
    }
  }

  fun typeAfterMethodCall(utils: MungoUtils, type: TypeMirror): MungoType? {
    if (type.kind != TypeKind.DECLARED) return null
    if (ClassUtils.isJavaLangObject(type)) return null

    val graph = utils.classUtils.visitClassTypeMirror(type) ?: return null

    val isNullable = type.annotationMirrors.any { MungoUtils.nullableAnnotations.contains(AnnotationUtils.annotationName(it)) }
    val stateAfterAnno = type.annotationMirrors.find { AnnotationUtils.areSameByName(it, MungoUtils.mungoEnsures) }
    val stateNames = MungoUtils.getAnnotationValue(stateAfterAnno) ?: return null

    val states = graph.getAllConcreteStates().filter { stateNames.contains(it.name) }

    val maybeNullableType = if (isNullable) MungoNullType.SINGLETON else MungoBottomType.SINGLETON

    return MungoUnionType.create(states.map { MungoStateType.create(graph, it) }.plus(maybeNullableType))
  }

  private val acceptedFinalTypes = MungoUnionType.create(listOf(MungoPrimitiveType.SINGLETON, MungoNullType.SINGLETON, MungoNoProtocolType.SINGLETON, MungoMovedType.SINGLETON, MungoEndedType.SINGLETON))
  val noProtocolTypes = MungoUnionType.create(listOf(MungoPrimitiveType.SINGLETON, MungoNullType.SINGLETON, MungoNoProtocolType.SINGLETON))
  val noProtocolOrMoved = MungoUnionType.create(listOf(MungoPrimitiveType.SINGLETON, MungoNullType.SINGLETON, MungoNoProtocolType.SINGLETON, MungoMovedType.SINGLETON))

}
