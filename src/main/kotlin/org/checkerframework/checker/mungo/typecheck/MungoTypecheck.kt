package org.checkerframework.checker.mungo.typecheck

import com.sun.source.tree.MethodInvocationTree
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.mungo.analysis.MungoValue
import org.checkerframework.checker.mungo.typestate.graph.Graph
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
      is MungoUnknownType -> "Cannot call ${TreeUtils.methodName(node)} on unknown"
      is MungoBottomType -> null // Allow operations on the BottomType to avoid propagating errors
      is MungoNoProtocolType -> null
      is MungoNullType -> "Cannot call ${TreeUtils.methodName(node)} because ${TreeUtils.getReceiverTree(node)} is null"
      is MungoEndedType -> "Cannot call ${TreeUtils.methodName(node)} because ${TreeUtils.getReceiverTree(node)} has ended its protocol"
      is MungoStateType -> {
        if (!info.state.transitions.entries.any { utils.methodUtils.sameMethod(tree, method, it.key) }) {
          "Cannot call ${TreeUtils.methodName(node)} on state ${info.state.name}"
        } else {
          null
        }
      }
      is MungoUnionType -> {
        val currentStates = mutableListOf<String>()
        val unexpectedStates = mutableListOf<String>()
        for (type in info.types) {
          when (type) {
            is MungoNullType -> {
              currentStates.add("#null")
              unexpectedStates.add("#null")
            }
            is MungoEndedType -> {
              currentStates.add("end")
              unexpectedStates.add("end")
            }
            is MungoStateType -> {
              currentStates.add(type.state.name)
              if (!type.state.transitions.entries.any { utils.methodUtils.sameMethod(tree, method, it.key) }) {
                unexpectedStates.add(type.state.name)
              }
            }
          }
        }
        if (unexpectedStates.size > 0) {
          "Cannot call ${TreeUtils.methodName(node)} on states ${unexpectedStates.joinToString(", ")}. (Inferred: ${currentStates.joinToString(", ")})"
        } else {
          null
        }
      }
    }
    if (error != null) {
      utils.err(error, node)
    }
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
