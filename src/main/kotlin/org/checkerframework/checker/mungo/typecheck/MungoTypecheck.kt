package org.checkerframework.checker.mungo.typecheck

import com.sun.source.tree.MethodInvocationTree
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.mungo.analysis.MungoValue
import org.checkerframework.checker.mungo.typestate.graph.states.DecisionState
import org.checkerframework.checker.mungo.typestate.graph.states.State
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.javacutil.TreeUtils

object MungoTypecheck {
  // True iff: sub contained in sup
  fun isSubtype(sub: MungoTypeInfo, sup: MungoTypeInfo): Boolean {
    return sub.graph === sup.graph && sup.states.containsAll(sub.states)
  }

  fun leastUpperBound(a1: MungoTypeInfo, a2: MungoTypeInfo): MungoTypeInfo? {
    return when {
      isSubtype(a1, a2) -> a2
      isSubtype(a2, a1) -> a1
      else -> return if (a1.graph == a2.graph) {
        val set = mutableSetOf<State>()
        set.addAll(a1.states)
        set.addAll(a2.states)
        MungoTypeInfo(a1.graph, set)
      } else {
        null
      }
    }
  }

  fun mostSpecific(a1: MungoTypeInfo, a2: MungoTypeInfo): MungoTypeInfo? {
    return when {
      isSubtype(a1, a2) -> a1
      isSubtype(a2, a1) -> a2
      else -> null
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
    if (MungoUtils.hasBottom(receiverValue.annotations)) {
      utils.err("Cannot call ${TreeUtils.methodName(node)} because ${TreeUtils.getReceiverTree(node)} has the bottom type", node)
      return
    }
    val info = receiverValue.getInfo() ?: return

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

  fun refine(utils: MungoUtils, tree: TreePath, info: MungoTypeInfo, method: Symbol.MethodSymbol, predicate: (String) -> Boolean): Set<State> {
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
