package org.checkerframework.checker.mungo.analysis

import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.typecheck.MungoConcreteType
import org.checkerframework.checker.mungo.typecheck.MungoNullType
import org.checkerframework.checker.mungo.typecheck.MungoType
import org.checkerframework.checker.mungo.typecheck.MungoTypecheck
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.dataflow.analysis.*
import org.checkerframework.dataflow.cfg.node.*
import org.checkerframework.framework.flow.CFAbstractTransfer
import javax.lang.model.element.ElementKind

class MungoTransfer(checker: MungoChecker, analysis: MungoAnalysis) : CFAbstractTransfer<MungoValue, MungoStore, MungoTransfer>(analysis) {

  private val c = checker

  private val getInfo = MungoValue::getInfo
  private val getPrevInfo = MungoValue::getPrevInfo

  private val allLabels: (String) -> Boolean = { true }

  // Use != to accept other labels as possible
  // (although if the method returns boolean, other labels would be invalid...)
  private val ifTrue: (String) -> Boolean = { it != "false" }
  private val ifFalse: (String) -> Boolean = { it != "true" }

  // Returns true if store changed
  private fun refineStore(tree: TreePath, method: Symbol.MethodSymbol, receiver: FlowExpressions.Receiver, store: MungoStore, predicate: (String) -> Boolean, getInfo: (MungoValue) -> MungoType?): Boolean {
    val prevValue = store.getValue(receiver)
    if (prevValue != null) {
      val prevInfo = getInfo(prevValue)
      if (prevInfo != null) {
        val newInfo = MungoTypecheck.refine(c.utils, tree, prevInfo, method, predicate)
        if (prevInfo != newInfo) {
          val newValue = MungoValue(prevValue, newInfo, prevInfo)
          store.replaceValue(receiver, newValue)
          return true
        }
      }
    }
    return false
  }

  // TODO force object to reach final state

  override fun visitMethodInvocation(n: MethodInvocationNode, input: TransferInput<MungoValue, MungoStore>): TransferResult<MungoValue, MungoStore> {
    val result = super.visitMethodInvocation(n, input)
    val method = n.target.method

    if (method !is Symbol.MethodSymbol || method.getKind() != ElementKind.METHOD) {
      return result
    }

    val receiver = FlowExpressions.internalReprOf(analysis.typeFactory, n.target.receiver)

    if (c.utils.methodUtils.returnsBoolean(method)) {
      val thenStore = result.thenStore
      val elseStore = result.elseStore
      val didChangeThen = refineStore(n.treePath, method, receiver, thenStore, ifTrue, getInfo)
      val didChangeElse = refineStore(n.treePath, method, receiver, elseStore, ifFalse, getInfo)
      return if (didChangeThen || didChangeElse) ConditionalTransferResult(result.resultValue, thenStore, elseStore, true) else result
    }

    return if (result.containsTwoStores()) {
      val thenStore = result.thenStore
      val elseStore = result.elseStore
      val didChangeThen = refineStore(n.treePath, method, receiver, thenStore, allLabels, getInfo)
      val didChangeElse = refineStore(n.treePath, method, receiver, elseStore, allLabels, getInfo)
      if (didChangeThen || didChangeElse) ConditionalTransferResult(result.resultValue, thenStore, elseStore, true) else result
    } else {
      val store = result.regularStore
      val didChange = refineStore(n.treePath, method, receiver, store, allLabels, getInfo)
      if (didChange) RegularTransferResult(result.resultValue, store, true) else result
    }
  }

  override fun visitCase(node: CaseNode, input: TransferInput<MungoValue, MungoStore>): TransferResult<MungoValue, MungoStore> {
    val result = super.visitCase(node, input)
    val assign = node.switchOperand as AssignmentNode
    val expression = assign.expression
    val caseOperand = node.caseOperand

    if (expression is MethodInvocationNode && caseOperand is FieldAccessNode) {
      val method = expression.target.method
      if (method !is Symbol.MethodSymbol || method.getKind() != ElementKind.METHOD) {
        return result
      }

      val receiver = FlowExpressions.internalReprOf(analysis.typeFactory, expression.target.receiver)
      val label = caseOperand.fieldName
      val thenStore = result.thenStore
      val elseStore = result.elseStore
      val didChangeThen = refineStore(expression.treePath, method, receiver, thenStore, { it == label }, getPrevInfo)
      val didChangeElse = refineStore(expression.treePath, method, receiver, elseStore, { it != label }, getPrevInfo)
      return if (didChangeThen || didChangeElse) ConditionalTransferResult(result.resultValue, thenStore, elseStore, true) else result
    }
    return result
  }

  override fun visitObjectCreation(node: ObjectCreationNode, input: TransferInput<MungoValue, MungoStore>): TransferResult<MungoValue, MungoStore> {
    val result = super.visitObjectCreation(node, input)
    val value = result.resultValue
    if (value != null) {
      // Refine resultValue to the initial state
      val currInfo = value.getInfo()
      if (currInfo is MungoConcreteType) {
        val newInfo = MungoConcreteType(currInfo.graph, setOf(currInfo.graph.getInitialState()))
        val newValue = MungoValue(value, newInfo)
        return if (result.containsTwoStores()) {
          ConditionalTransferResult(newValue, result.thenStore, result.elseStore, false)
        } else {
          RegularTransferResult(newValue, result.regularStore, false)
        }
      }
    }
    return result
  }

  override fun visitNullLiteral(n: NullLiteralNode, p: TransferInput<MungoValue, MungoStore>): TransferResult<MungoValue, MungoStore> {
    val result = super.visitNullLiteral(n, p)
    val value = result.resultValue
    if (value != null) {
      // Replace the resultValue to be the MungoNullType instead of MungoBottomType
      val newInfo = MungoNullType()
      val newValue = MungoValue(value, newInfo)
      return if (result.containsTwoStores()) {
        ConditionalTransferResult(newValue, result.thenStore, result.elseStore, false)
      } else {
        RegularTransferResult(newValue, result.regularStore, false)
      }
    }
    return result
  }

}
