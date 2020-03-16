package org.checkerframework.checker.mungo.analysis

import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.code.Type
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.typecheck.MungoTypeInfo
import org.checkerframework.checker.mungo.typecheck.MungoTypecheck
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.dataflow.analysis.*
import org.checkerframework.dataflow.cfg.node.AssignmentNode
import org.checkerframework.dataflow.cfg.node.CaseNode
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode
import org.checkerframework.framework.flow.CFAbstractTransfer
import javax.lang.model.element.ElementKind

class MungoTransfer(checker: MungoChecker, analysis: MungoAnalysis) : CFAbstractTransfer<MungoValue, MungoStore, MungoTransfer>(analysis) {

  private val c = checker

  // Returns true if store changed
  private fun refineStore(tree: TreePath, method: Symbol.MethodSymbol, receiver: FlowExpressions.Receiver, store: MungoStore, label: String?): Boolean {
    val value = store.getValue(receiver)
    if (value != null) {
      val info = MungoUtils.getInfoFromAnnotations(value.annotations)
      if (info != null) {
        val newInfo = MungoTypeInfo.build(c.utils, info.graph, MungoTypecheck.refine(c.utils, tree, info, method, label))
        if (info != newInfo) {
          store.replaceValue(receiver, analysis.createAbstractValue(setOf(newInfo), value.underlyingType))
          return true
        }
      }
    }
    return false
  }

  // TODO deal with switch statements
  // TODO force object to reach final state
  // TODO analyze this, might be useful: store.updateForMethodCall

  override fun visitMethodInvocation(n: MethodInvocationNode, input: TransferInput<MungoValue, MungoStore>): TransferResult<MungoValue, MungoStore> {
    val result = super.visitMethodInvocation(n, input)
    val method = n.target.method

    if (method !is Symbol.MethodSymbol || method.getKind() != ElementKind.METHOD) {
      return result
    }

    val receiver = FlowExpressions.internalReprOf(analysis.typeFactory, n.target.receiver)

    if (result.containsTwoStores()) {
      val thenStore = result.thenStore
      val elseStore = result.elseStore
      val returnsBool = c.utils.methodReturnsBoolean(n.treePath, method)
      val didChangeThen = refineStore(n.treePath, method, receiver, thenStore, if (returnsBool) "true" else null)
      val didChangeElse = refineStore(n.treePath, method, receiver, elseStore, if (returnsBool) "false" else null)
      return if (didChangeThen || didChangeElse) ConditionalTransferResult(result.resultValue, thenStore, elseStore, true) else result
    }

    val store = result.regularStore
    val didChange = refineStore(n.treePath, method, receiver, store, null)
    return if (didChange) RegularTransferResult(result.resultValue, store, true) else result
  }

  override fun visitCase(node: CaseNode, input: TransferInput<MungoValue, MungoStore>): TransferResult<MungoValue, MungoStore> {
    val result = super.visitCase(node, input)
    val store = input.regularStore

    val assign = node.switchOperand as AssignmentNode
    val expression = assign.expression

    if (expression is MethodInvocationNode) {
      val caseValue = input.getValueOfSubNode(node.caseOperand)
      val switchValue = store.getValue(FlowExpressions.internalReprOf(analysis.typeFactory, assign.target))
      val receiver = FlowExpressions.internalReprOf(analysis.typeFactory, expression.target.receiver)

      println(expression)
      println(store.getValue(receiver))
      println(caseValue)
      println(caseValue?.underlyingType as Type?)
      println(switchValue)
      println()
    }
    return result
  }

  override fun visitObjectCreation(node: ObjectCreationNode, input: TransferInput<MungoValue, MungoStore>): TransferResult<MungoValue, MungoStore> {
    val result = super.visitObjectCreation(node, input)
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
