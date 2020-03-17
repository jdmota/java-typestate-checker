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
  fun isSubtype(sub: MungoType, sup: MungoType): Boolean {
    if (sub is MungoBottomType) {
      return true
    }
    if (sub is MungoConcreteType) {
      if (sup is MungoConcreteType) {
        return sub.graph === sup.graph && sup.states.containsAll(sub.states)
      }
      return sup is MungoUnknownType
    }
    if (sub is MungoUnknownType) {
      return sup is MungoUnknownType
    }
    return false
  }

  fun leastUpperBound(a1: MungoType, a2: MungoType): MungoType {
    return when (a1) {
      is MungoBottomType -> a2
      is MungoConcreteType -> when (a2) {
        is MungoBottomType -> a1
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
        } else {
          MungoUnknownType()
        }
        is MungoUnknownType -> a2
      }
      is MungoUnknownType -> a1
    }
  }

  fun mostSpecific(a1: MungoType, a2: MungoType): MungoType? {
    return when (a1) {
      is MungoBottomType -> a1
      is MungoConcreteType -> when (a2) {
        is MungoBottomType -> a2
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
    val info = receiverValue.getInfo()

    if (info is MungoBottomType) {
      utils.err("Cannot call ${TreeUtils.methodName(node)} because ${TreeUtils.getReceiverTree(node)} has the bottom type", node)
      return
    }

    if (info is MungoUnknownType) {
      utils.err("Cannot call ${TreeUtils.methodName(node)}. (Unknown states)", node)
      return
    }

    if (info !is MungoConcreteType) throw AssertionError("never")

    if (info.states.isEmpty()) {
      utils.err("Cannot call ${TreeUtils.methodName(node)}. (Inferred no states)", node)
      return
    }

    val unexpectedStates = mutableListOf<State>()
    for (state in info.states) {
      if (!state.transitions.entries.any { utils.methodUtils.sameMethod(tree, method, it.key) }) {
        unexpectedStates.add(state)
      }
    }
    if (unexpectedStates.size > 0) {
      val currentStates = info.states.joinToString(", ") { it.name }
      val wrongStates = unexpectedStates.joinToString(", ") { it.name }
      utils.err("Cannot call ${TreeUtils.methodName(node)} on states $wrongStates. (Inferred: $currentStates)", node)
    }
  }

  fun refine(utils: MungoUtils, tree: TreePath, info: MungoConcreteType, method: Symbol.MethodSymbol, predicate: (String) -> Boolean): Set<State> {
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
