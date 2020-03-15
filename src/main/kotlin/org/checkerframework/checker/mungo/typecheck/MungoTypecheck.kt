package org.checkerframework.checker.mungo.typecheck

import com.sun.source.tree.MethodInvocationTree
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.typestate.graph.states.DecisionState
import org.checkerframework.checker.mungo.typestate.graph.states.State
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.checker.mungo.utils.MungoUtils.Companion.castAnnotation
import org.checkerframework.javacutil.TreeUtils
import javax.lang.model.element.AnnotationMirror

object MungoTypecheck {
  // pre: "sub" and "sup" are @MungoInfo annotations
  fun isSubType(sub: AnnotationMirror, sup: AnnotationMirror): Boolean {
    return isSubType(castAnnotation(sub), castAnnotation(sup))
  }

  fun isSubType(sub: MungoTypeInfo, sup: MungoTypeInfo): Boolean {
    return sub.graph === sup.graph && sup.states.containsAll(sub.states)
  }

  fun check(utils: MungoUtils, unit: JCTree.JCCompilationUnit, annotations: Set<AnnotationMirror>, node: MethodInvocationTree, method: Symbol.MethodSymbol) {
    if (MungoUtils.hasBottom(annotations)) {
      utils.err("Cannot call ${TreeUtils.methodName(node)} because ${TreeUtils.getReceiverTree(node)} has the bottom type", node)
      return
    }
    val info = MungoUtils.getInfoFromAnnotations(annotations) ?: return

    if (info.states.isEmpty()) {
      utils.err("Cannot call ${TreeUtils.methodName(node)}. (Inferred no states)", node)
      return
    }

    val unexpectedStates = mutableListOf<State>()
    for (state in info.states) {
      if (!state.transitions.entries.any { utils.sameMethod(unit, method, it.key) }) {
        unexpectedStates.add(state)
      }
    }
    if (unexpectedStates.size > 0) {
      val currentStates = info.states.joinToString(", ") { it.name }
      val wrongStates = unexpectedStates.joinToString(", ") { it.name }
      utils.err("Cannot call ${TreeUtils.methodName(node)} on states $wrongStates. (Inferred: $currentStates)", node)
    }
  }

  fun refine(utils: MungoUtils, unit: JCTree.JCCompilationUnit, info: MungoTypeInfo, method: Symbol.MethodSymbol, label: String?): Set<State> {
    // Given the possible current states, produce a set of possible destination states
    return info.states.flatMap { state ->
      val dest = state.transitions.entries.find { utils.sameMethod(unit, method, it.key) }?.value
      when (dest) {
        is State -> listOf(dest)
        is DecisionState ->
          if (label == null) {
            dest.transitions.values
          } else {
            val dest2 = dest.transitions.entries.find { it.key.label == label }?.value
            if (dest2 == null) listOf() else listOf(dest2)
          }
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
