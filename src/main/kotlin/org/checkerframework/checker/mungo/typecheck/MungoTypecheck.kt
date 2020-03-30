package org.checkerframework.checker.mungo.typecheck

import com.sun.source.tree.MethodInvocationTree
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.mungo.analysis.MungoValue
import org.checkerframework.checker.mungo.typestate.graph.states.DecisionState
import org.checkerframework.checker.mungo.typestate.graph.states.State
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.javacutil.TreeUtils

object MungoTypecheck {
  fun check(
    utils: MungoUtils,
    tree: TreePath,
    receiverValue: MungoValue?,
    node: MethodInvocationTree,
    method: Symbol.MethodSymbol
  ) {
    if (receiverValue == null) {
      return
    }
    val error = when (val info = receiverValue.info) {
      is MungoUnknownType -> createErrorMsg(node, isUnknown = true)
      is MungoBottomType -> null // Allow operations on the BottomType to avoid propagating errors
      is MungoNoProtocolType -> null
      is MungoNullType -> createErrorMsg(node, isNull = true)
      is MungoEndedType -> createErrorMsg(node, isEnded = true)
      is MungoStateType -> {
        if (info.state.transitions.entries.any { utils.methodUtils.sameMethod(tree, method, it.key) }) {
          null
        } else {
          createErrorMsg(node, unexpectedStates = listOf(info.state.name), currentStates = listOf(info.state.name))
        }
      }
      is MungoUnionType -> {
        val currentStates = mutableListOf<String>()
        val unexpectedStates = mutableListOf<String>()
        var isNull = false
        var isEnded = false
        for (type in info.types) {
          when (type) {
            is MungoNullType -> isNull = true
            is MungoEndedType -> isEnded = true
            is MungoStateType -> {
              currentStates.add(type.state.name)
              if (!type.state.transitions.entries.any { utils.methodUtils.sameMethod(tree, method, it.key) }) {
                unexpectedStates.add(type.state.name)
              }
            }
          }
        }
        if (isNull || isEnded || unexpectedStates.size > 0) {
          createErrorMsg(node, isNull = isNull, isEnded = isEnded, unexpectedStates = unexpectedStates, currentStates = currentStates)
        } else {
          null
        }
      }
    }
    if (error != null) {
      utils.err(error, node)
    }
  }

  private fun createErrorMsg(
    node: MethodInvocationTree,
    isUnknown: Boolean = false,
    isNull: Boolean = false,
    isEnded: Boolean = false,
    unexpectedStates: List<String> = listOf(),
    currentStates: List<String> = listOf()
  ): String {
    val m = TreeUtils.methodName(node)
    val items = mutableListOf<String>()
    if (isUnknown) items.add("on unknown")
    if (isNull) items.add("on null")
    if (isEnded) items.add("on ended protocol")
    if (unexpectedStates.isNotEmpty()) items.add("on state${if (unexpectedStates.size > 1) "s" else ""} ${unexpectedStates.joinToString(", ")} (got: ${currentStates.joinToString(", ")})")
    return "Cannot call $m ${items.joinToString(", ")}"
  }

  fun refine(utils: MungoUtils, tree: TreePath, type: MungoType, method: Symbol.MethodSymbol, predicate: (String) -> Boolean): MungoType {
    return when (type) {
      // Unknown stays Unknown
      is MungoUnknownType -> MungoUnknownType.SINGLETON
      // Bottom stays bottom
      is MungoBottomType -> MungoBottomType.SINGLETON
      // Calling a method on null would produce an exception, so the method call has bottom type
      is MungoNullType -> MungoBottomType.SINGLETON
      // Since the "end" has no transitions, we refine to an empty set of states
      is MungoEndedType -> MungoBottomType.SINGLETON
      // Objects with no protocol, stay like that
      is MungoNoProtocolType -> MungoNoProtocolType.SINGLETON
      // Refine...
      is MungoUnionType -> MungoUnionType.create(type.types.map { refine(utils, tree, it, method, predicate) })
      is MungoStateType -> MungoUnionType.create(refine(utils, tree, type, method, predicate))
    }
  }

  private fun refine(utils: MungoUtils, tree: TreePath, type: MungoStateType, method: Symbol.MethodSymbol, predicate: (String) -> Boolean): List<MungoType> {
    // Given a current state, produce a set of possible destination states
    val dest = type.state.transitions.entries.find { utils.methodUtils.sameMethod(tree, method, it.key) }?.value
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
}
