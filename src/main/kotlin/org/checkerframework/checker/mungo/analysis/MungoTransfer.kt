package org.checkerframework.checker.mungo.analysis

import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.typecheck.MungoTypeInfo
import org.checkerframework.checker.mungo.typestate.graph.states.DecisionState
import org.checkerframework.checker.mungo.typestate.graph.states.State
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.dataflow.analysis.*
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode
import org.checkerframework.framework.flow.CFAbstractTransfer

class MungoTransfer(checker: MungoChecker, analysis: MungoAnalysis) : CFAbstractTransfer<MungoValue, MungoStore, MungoTransfer>(analysis) {

  private val c = checker

  private fun refine(unit: JCTree.JCCompilationUnit, info: MungoTypeInfo, method: Symbol.MethodSymbol, label: String?): MungoTypeInfo {
    println("$method label: $label")
    println("Current possible states: " + info.states)

    // Given the possible current states, produce a set of possible destination states
    val newStates = info.states.flatMap {
      val dest = it.transitions.entries.find { it2 -> c.utils.sameMethod(unit, method, it2.key) }?.value
      when (dest) {
        is State -> listOf(dest)
        is DecisionState -> {
          if (label == null) dest.transitions.values else {
            val dest2 = dest.transitions.entries.find { it2 -> it2.key.label == label }?.value
            if (dest2 == null) listOf() else listOf(dest2)
          }
        }
        // The method call is not allowed in this state,
        // so return an empty list (imagine this as the bottom type).
        // The union of some type T with the bottom type, is T,
        // which is fine. The MungoVisitor will later ensure a call is safe
        // by checking that the method is available in all states.
        else -> listOf()
      }
    }.toSet()

    println("New possible states: $newStates")
    println()

    return MungoTypeInfo.build(c.utils, info.graph, newStates)
  }

  private fun refineStore(unit: JCTree.JCCompilationUnit, method: Symbol.MethodSymbol, receiver: FlowExpressions.Receiver, store: MungoStore, label: String?): Boolean {
    val value = store.getValue(receiver)
    if (value != null) {
      val info = MungoUtils.getInfoFromAnnotations(value.annotations)
      if (info != null) {
        val newInfo = refine(unit, info, method, label)
        if (info != newInfo) {
          // Update thenStore
          store.replaceValue(receiver, analysis.createAbstractValue(setOf(newInfo), value.underlyingType))
          return true
        }
      }
    }
    return false
  }

  // TODO deal with switch statements
  // TODO force object to reach final state

  override fun visitMethodInvocation(n: MethodInvocationNode, input: TransferInput<MungoValue, MungoStore>): TransferResult<MungoValue, MungoStore> {
    val result = super.visitMethodInvocation(n, input)
    val method = n.target.method as Symbol.MethodSymbol
    val receiver = FlowExpressions.internalReprOf(analysis.typeFactory, n.target.receiver)
    val unit = n.treePath.compilationUnit as JCTree.JCCompilationUnit

    if (result.containsTwoStores()) {
      val thenStore = result.thenStore
      val elseStore = result.elseStore
      val didChangeThen = refineStore(unit, method, receiver, thenStore, "true")
      val didChangeElse = refineStore(unit, method, receiver, elseStore, "false")
      //println("thenStore $thenStore")
      //println("elseStore $elseStore")
      return if (didChangeThen || didChangeElse) ConditionalTransferResult(result.resultValue, thenStore, elseStore, true) else result
    }

    val store = result.regularStore
    val didChange = refineStore(unit, method, receiver, store, null)
    //println("store $store")
    return if (didChange) RegularTransferResult(result.resultValue, store, true) else result
  }

  override fun visitObjectCreation(n: ObjectCreationNode, p: TransferInput<MungoValue, MungoStore>): TransferResult<MungoValue, MungoStore> {
    val result = super.visitObjectCreation(n, p)
    val value = result.resultValue
    if (value != null) {
      // Refine resultValue to the initial state
      val info = MungoUtils.getInfoFromAnnotations(value.annotations)
      if (info != null) {
        val newInfo = MungoTypeInfo.build(c.utils, info.graph, setOf(info.graph.getInitialState()))
        // Check it changed
        if (info != newInfo) {
          val newValue = analysis.createAbstractValue(setOf(newInfo), value.underlyingType)
          return if (result.containsTwoStores())
            ConditionalTransferResult(newValue, result.thenStore, result.elseStore, true)
          else RegularTransferResult(newValue, result.regularStore, true)
        }
      }
    }
    return result
  }

}
