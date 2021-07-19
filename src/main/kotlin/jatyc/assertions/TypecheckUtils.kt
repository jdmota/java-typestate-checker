package jatyc.assertions

import com.sun.source.tree.MethodInvocationTree
import com.sun.tools.javac.code.Symbol
import jatyc.typestate.graph.DecisionState
import jatyc.typestate.graph.Graph
import jatyc.typestate.graph.State
import jatyc.utils.ClassUtils
import jatyc.utils.JTCUtils
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.javacutil.TreeUtils
import javax.lang.model.type.TypeKind
import javax.lang.model.type.TypeMirror

object TypecheckUtils {
  fun available(utils: JTCUtils, graph: Graph, method: Symbol.MethodSymbol): List<JTCType> {
    val env = graph.getEnv()
    return graph.getAllConcreteStates().filter { state ->
      // TODO with generics support, replace sameErasedMethod for sameMethod
      state.transitions.entries.any { utils.methodUtils.sameErasedMethod(env, method, it.key) }
    }.map { JTCStateType.create(graph, it) }
  }

  fun check(
    utils: JTCUtils,
    info: JTCType,
    node: MethodInvocationTree,
    method: Symbol.MethodSymbol
  ): Boolean {
    val error = when (info) {
      is JTCUnknownType -> createErrorMsg(node, isUnknown = true)
      is JTCObjectType -> createErrorMsg(node, isObject = true)
      is JTCBottomType -> null // Allow operations on the BottomType to avoid propagating errors
      is JTCNoProtocolType -> null // Any call allowed on NoProtocol
      is JTCPrimitiveType -> null // Calls on primitive values are not possible, so just ignore
      is JTCNullType -> createErrorMsg(node, isNull = true)
      is JTCEndedType -> createErrorMsg(node, isEnded = true)
      is JTCMovedType -> createErrorMsg(node, isMoved = true)
      is JTCStateType -> {
        val env = info.graph.getEnv()
        // TODO with generics support, replace sameErasedMethod for sameMethod
        if (info.state.transitions.entries.any { utils.methodUtils.sameErasedMethod(env, method, it.key) }) {
          null
        } else {
          createErrorMsg(node, unexpectedStates = listOf(info.state.name), currentStates = listOf(info.state.name))
        }
      }
      is JTCUnionType -> {
        val currentStates = mutableListOf<String>()
        val unexpectedStates = mutableListOf<String>()
        var isObject = false
        var isNull = false
        var isEnded = false
        var isMoved = false
        for (type in info.types) {
          when (type) {
            is JTCObjectType -> isObject = true
            is JTCNullType -> isNull = true
            is JTCEndedType -> isEnded = true
            is JTCMovedType -> isMoved = true
            is JTCPrimitiveType -> {
              // Calls on primitive values are not possible, so just ignore
            }
            is JTCNoProtocolType -> {
              // Any call allowed on NoProtocol
            }
            is JTCStateType -> {
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

  fun refine(utils: JTCUtils, type: JTCType, method: Symbol.MethodSymbol, predicate: (String) -> Boolean): JTCType {
    return when (type) {
      // Unknown stays Unknown
      is JTCUnknownType -> JTCUnknownType.SINGLETON
      // Object stays Object
      is JTCObjectType -> JTCObjectType.SINGLETON
      // Bottom stays bottom
      is JTCBottomType -> JTCBottomType.SINGLETON
      // Calling a method on null would produce an exception, so the method call has bottom type
      is JTCNullType -> JTCBottomType.SINGLETON
      // Since the "end" has no transitions, we refine to an empty set of states
      is JTCEndedType -> JTCBottomType.SINGLETON
      // Refine to bottom to avoid propagating errors
      is JTCMovedType -> JTCBottomType.SINGLETON
      // Calls on primitive values not possible anyway
      is JTCPrimitiveType -> JTCBottomType.SINGLETON
      // Objects with no protocol, stay like that
      is JTCNoProtocolType -> JTCNoProtocolType.SINGLETON
      // Refine...
      is JTCUnionType -> JTCUnionType.create(type.types.map { refine(utils, it, method, predicate) })
      is JTCStateType -> JTCUnionType.create(refine(utils, type, method, predicate))
    }
  }

  private fun refine(utils: JTCUtils, type: JTCStateType, method: Symbol.MethodSymbol, predicate: (String) -> Boolean): List<JTCType> {
    val env = type.graph.getEnv()
    // Given a current state, produce a set of possible destination states
    return when (val dest = type.state.transitions.entries.find { utils.methodUtils.sameMethod(env, method, it.key) }?.value) {
      is State -> listOf(JTCStateType.create(type.graph, dest))
      is DecisionState -> dest.transitions.entries.filter { predicate(it.key.label) }.map { JTCStateType.create(type.graph, it.value) }
      // The method call is not allowed in this state,
      // so return an empty list (imagine this as the bottom type).
      // The union of some type T with the bottom type, is T,
      // which is fine. The type-checker will later ensure a call is safe
      // by checking that the method is available in all states.
      else -> listOf()
    }
  }

  fun refineToNonNull(type: JTCType): JTCType {
    return when (type) {
      // Refine...
      is JTCNullType -> JTCBottomType.SINGLETON
      is JTCUnionType -> JTCUnionType.create(type.types.map { refineToNonNull(it) })
      // Others...
      else -> type
    }
  }

  fun refineToNull(type: JTCType): JTCType {
    return if (JTCNullType.SINGLETON.isSubtype(type)) JTCNullType.SINGLETON else JTCBottomType.SINGLETON
  }

  fun objectCreation(utils: JTCUtils, type: TypeMirror): JTCType {
    return if (ClassUtils.isJavaLangObject(type)) {
      JTCObjectType.SINGLETON
    } else {
      val graph = utils.classUtils.getGraph(type)
      if (graph == null) {
        JTCNoProtocolType.SINGLETON
      } else {
        JTCStateType.create(graph, graph.getInitialState())
      }
    }
  }

  fun typeAfterMethodCall(utils: JTCUtils, type: TypeMirror): JTCType? {
    if (type.kind != TypeKind.DECLARED) return null
    if (ClassUtils.isJavaLangObject(type)) return null

    val graph = utils.classUtils.getGraph(type) ?: return null

    val isNullable = type.annotationMirrors.any { JTCUtils.nullableAnnotations.contains(AnnotationUtils.annotationName(it)) }
    val stateAfterAnno = type.annotationMirrors.find { AnnotationUtils.areSameByName(it, JTCUtils.jtcEnsuresAnno) }
    val stateNames = JTCUtils.getAnnotationValue(stateAfterAnno) ?: return null

    val states = graph.getAllConcreteStates().filter { stateNames.contains(it.name) }

    val maybeNullableType = if (isNullable) JTCNullType.SINGLETON else JTCBottomType.SINGLETON

    return JTCUnionType.create(states.map { JTCStateType.create(graph, it) }.plus(maybeNullableType))
  }

  val noProtocolOrMoved = JTCUnionType.create(listOf(JTCPrimitiveType.SINGLETON, JTCNullType.SINGLETON, JTCNoProtocolType.SINGLETON, JTCMovedType.SINGLETON))

}
