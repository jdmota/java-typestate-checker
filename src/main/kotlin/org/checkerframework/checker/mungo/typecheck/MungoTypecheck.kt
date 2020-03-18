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
  private val unknown = MungoUnknownType()

  // bottom <: concreteType <: unknown
  // bottom <: nullType <: unknown
  // concreteType and nullType are not comparable, the leastUpperBound of them is unknown
  // Maybe in the future we can create a unionType, to give more concrete error information

  fun leastUpperBound(a1: MungoType, a2: MungoType): MungoType {
    return when (a1) {
      is MungoBottomType -> a2
      is MungoNullType -> when (a2) {
        is MungoBottomType -> a1
        is MungoNullType -> a1
        is MungoConcreteType -> unknown
        is MungoUnknownType -> a2
      }
      is MungoConcreteType -> when (a2) {
        is MungoBottomType -> a1
        is MungoNullType -> unknown
        is MungoConcreteType -> if (a1.graph == a2.graph) {
          when {
            a1.states.containsAll(a2.states) -> a1
            a2.states.containsAll(a1.states) -> a2
            else -> {
              val set = mutableSetOf<State>()
              set.addAll(a1.states)
              set.addAll(a2.states)
              MungoConcreteType(a1.graph, set)
            }
          }
        } else unknown
        is MungoUnknownType -> a2
      }
      is MungoUnknownType -> a1
    }
  }

  fun mostSpecific(a1: MungoType, a2: MungoType): MungoType? {
    return when (a1) {
      is MungoBottomType -> a1
      is MungoNullType -> when (a2) {
        is MungoBottomType -> a2
        is MungoNullType -> a2
        is MungoConcreteType -> null
        is MungoUnknownType -> a1
      }
      is MungoConcreteType -> when (a2) {
        is MungoBottomType -> a2
        is MungoNullType -> null
        is MungoConcreteType -> if (a1.graph == a2.graph) {
          when {
            a1.states.containsAll(a2.states) -> a2
            a2.states.containsAll(a1.states) -> a1
            else -> null
          }
        } else null
        is MungoUnknownType -> a1
      }
      is MungoUnknownType -> a2
    }
  }

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
    val error = when (val info = receiverValue.getInfo()) {
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
      // Call a method on null would produce an exception, so the method call has bottom type
      is MungoNullType -> MungoBottomType()
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
