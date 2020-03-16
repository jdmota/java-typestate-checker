package org.checkerframework.checker.mungo.analysis

import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.code.Type
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.typecheck.MungoTypeInfo
import org.checkerframework.checker.mungo.typecheck.MungoTypecheck
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.dataflow.analysis.*
import org.checkerframework.dataflow.cfg.node.*
import org.checkerframework.framework.flow.CFAbstractTransfer
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.javacutil.TypesUtils
import java.lang.Exception
import java.lang.RuntimeException
import javax.lang.model.element.ElementKind

class MungoTransfer(checker: MungoChecker, analysis: MungoAnalysis) : CFAbstractTransfer<MungoValue, MungoStore, MungoTransfer>(analysis) {

  private val c = checker
  private val a = analysis

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

    if (c.utils.methodUtils.returnsBoolean(method)) {
      val thenStore = result.thenStore
      val elseStore = result.elseStore
      val didChangeThen = refineStore(n.treePath, method, receiver, thenStore, "true")
      val didChangeElse = refineStore(n.treePath, method, receiver, elseStore, "false")
      return if (didChangeThen || didChangeElse) ConditionalTransferResult(result.resultValue, thenStore, elseStore, true) else result
    }

    if (c.utils.methodUtils.returnsEnum(method)) {
      val returnType = method.returnType as Type.ClassType
      val returnSym = returnType.tsym as Symbol.ClassSymbol
      val members = returnSym.members()
      val labels = members.symbols.filter { it.isEnum }.map { it.name.toString() }

      // Do not modify directly
      val previousStore = result.regularStore

      // Did any store change?
      var didChange = false

      // Refine to all possible states
      val mainStore = previousStore.copy()
      didChange = refineStore(n.treePath, method, receiver, mainStore, null) || didChange

      // If the enum has no labels
      if (labels.isEmpty()) {
        return if (didChange) RegularTransferResult(result.resultValue, mainStore, true) else result
      }

      // Refine to specific labels
      val map = mutableMapOf<String, MungoStore>()
      for (label in labels) {
        val store = previousStore.copy()
        didChange = refineStore(n.treePath, method, receiver, store, label) || didChange
        map[label] = store
      }

      return if (didChange) RegularTransferResult(result.resultValue, MungoStoreWithCases(map, mainStore), true) else result
    }

    val store = result.regularStore
    val didChange = refineStore(n.treePath, method, receiver, store, null)
    return if (didChange) RegularTransferResult(result.resultValue, store, true) else result
  }

  // FIXME might not work... are we propagating the MungoStoreWithCases stores farther in an incorrect way?

  override fun visitCase(node: CaseNode, input: TransferInput<MungoValue, MungoStore>): TransferResult<MungoValue, MungoStore> {
    val result = super.visitCase(node, input)
    val store = input.regularStore

    val assign = node.switchOperand as AssignmentNode
    val expression = assign.expression
    val caseOperand = node.caseOperand

    if (expression is MethodInvocationNode && caseOperand is FieldAccessNode && store is MungoStoreWithCases) {
      val label = caseOperand.fieldName
      val caseStore = store.caseStores[label]
      if (caseStore != null) {
        return RegularTransferResult(result.resultValue, caseStore, true)
      }
      // TODO return ConditionalResult, with the other combined cases?
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
          return if (result.containsTwoStores()) {
            ConditionalTransferResult(newValue, result.thenStore, result.elseStore, false)
          } else {
            RegularTransferResult(newValue, result.regularStore, false)
          }
        }
      }
    }
    return result
  }

}
