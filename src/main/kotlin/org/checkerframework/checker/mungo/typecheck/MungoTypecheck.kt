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
      is MungoBottomType -> "Cannot call ${TreeUtils.methodName(node)} because ${TreeUtils.getReceiverTree(node)} has the bottom type"
      is MungoNullType -> "Cannot call ${TreeUtils.methodName(node)} because ${TreeUtils.getReceiverTree(node)} is null"
      is MungoUnknownType -> "Cannot call ${TreeUtils.methodName(node)}. (Unknown states)"
      is MungoConcreteType -> {
        if (info.states.isEmpty()) {
          "Cannot call ${TreeUtils.methodName(node)}. (Inferred no states)"
        } else {
          val unexpectedStates = mutableListOf<State>()
          for (state in info.states) {
            if (!state.transitions.entries.any { utils.methodUtils.sameMethod(tree, method, it.key) }) {
              unexpectedStates.add(state)
            }
          }
          if (unexpectedStates.size > 0) {
            val currentStates = info.states.joinToString(", ") { it.name }
            val wrongStates = unexpectedStates.joinToString(", ") { it.name }
            "Cannot call ${TreeUtils.methodName(node)} on states $wrongStates. (Inferred: $currentStates)"
          } else {
            null
          }
        }
      }
    }
    if (error != null) {
      utils.err(error, node)
    }
  }

  fun refine(utils: MungoUtils, tree: TreePath, info: MungoType, method: Symbol.MethodSymbol, predicate: (String) -> Boolean): MungoType {
    return when (info) {
      is MungoBottomType -> info
      // Calling a method on null would produce an exception, so the method call has bottom type
      is MungoNullType -> MungoBottomType.SINGLETON
      is MungoUnknownType -> info
      is MungoConcreteType -> MungoConcreteType(info.graph, refine(utils, tree, info, method, predicate))
    }
  }

  private fun refine(utils: MungoUtils, tree: TreePath, info: MungoConcreteType, method: Symbol.MethodSymbol, predicate: (String) -> Boolean): Set<State> {
    // Given the possible current states, produce a set of possible destination states
    return info.states.flatMap { state ->
      val dest = state.transitions.entries.find { utils.methodUtils.sameMethod(tree, method, it.key) }?.value
      when (dest) {
        is State -> listOf(dest)
        is DecisionState -> dest.transitions.entries.filter { predicate(it.key.label) }.map { it.value }
        // The method call is not allowed in this state,
        // so return an empty list (imagine this as the bottom type).
        // The union of some type T with the bottom type, is T,
        // which is fine. The MungoVisitor will later ensure a call is safe
        // by checking that the method is available in all states.
        else -> listOf()
      }
    }.toSet()
  }
}
