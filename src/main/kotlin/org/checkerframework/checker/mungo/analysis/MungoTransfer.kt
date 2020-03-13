package org.checkerframework.checker.mungo.analysis

import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.typecheck.MungoTypeInfo
import org.checkerframework.checker.mungo.typestate.graph.states.DecisionState
import org.checkerframework.checker.mungo.typestate.graph.states.State
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.dataflow.analysis.ConditionalTransferResult
import org.checkerframework.dataflow.analysis.FlowExpressions
import org.checkerframework.dataflow.analysis.TransferInput
import org.checkerframework.dataflow.analysis.TransferResult
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode
import org.checkerframework.framework.flow.CFAbstractTransfer

class MungoTransfer(checker: MungoChecker, analysis: MungoAnalysis) : CFAbstractTransfer<MungoValue, MungoStore, MungoTransfer>(analysis) {

  private val c = checker

  private fun refine(unit: JCTree.JCCompilationUnit, info: MungoTypeInfo, method: Symbol.MethodSymbol, ifOrElse: Boolean): MungoTypeInfo {
    println("$method if/else: $ifOrElse")
    println("Current possible states: " + info.states)

    // Given the possible current states, produce a set of possible destination states
    val newStates = info.states.flatMap {
      val dest = it.transitions.entries.find { it2 -> c.utils.sameMethod(unit, method, it2.key) }?.value
      when (dest) {
        is State -> listOf(dest)
        is DecisionState -> {
          val label = if (ifOrElse) "true" else "false"
          val dest2 = dest.transitions.entries.find { it2 -> it2.key.label == label }?.value
          if (dest2 == null) dest.transitions.values else listOf(dest2)
        }
        // The method call is not allowed in this state
        // Object might be in any state
        // FIXME hum...??
        else -> info.graph.getAllConcreteStates()
      }
    }.toSet()

    println("New possible states: $newStates")
    println()

    return MungoTypeInfo.build(c.elementUtils, info.graph, newStates)
  }

  private fun refineStore(unit: JCTree.JCCompilationUnit, method: Symbol.MethodSymbol, receiver: FlowExpressions.Receiver, store: MungoStore, ifOrElse: Boolean) {
    val value = store.getValue(receiver)
    if (value != null) {
      val info = MungoUtils.getInfoFromAnnotations(value.annotations)
      if (info != null) {
        val newInfo = refine(unit, info, method, ifOrElse)
        // Update thenStore
        store.replaceValue(receiver, analysis.createAbstractValue(setOf(newInfo), value.underlyingType))
      }
    }
  }

  // TODO deal with switch statements
  // TODO force object to reach final state

  override fun visitMethodInvocation(n: MethodInvocationNode, input: TransferInput<MungoValue, MungoStore>): TransferResult<MungoValue, MungoStore> {
    val result = super.visitMethodInvocation(n, input)
    val method = n.target.method as Symbol.MethodSymbol
    val receiver = FlowExpressions.internalReprOf(analysis.typeFactory, n.target.receiver)
    val unit = n.treePath.compilationUnit as JCTree.JCCompilationUnit

    val thenStore = result.thenStore
    val elseStore = result.elseStore

    refineStore(unit, method, receiver, thenStore, true)
    refineStore(unit, method, receiver, elseStore, false)

    return ConditionalTransferResult(result.resultValue, thenStore, elseStore);
  }
}
