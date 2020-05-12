package org.checkerframework.checker.mungo.analysis

import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory
import org.checkerframework.dataflow.analysis.Store
import org.checkerframework.dataflow.analysis.Store.FlowRule
import org.checkerframework.dataflow.analysis.TransferInput
import org.checkerframework.dataflow.analysis.TransferResult
import org.checkerframework.dataflow.cfg.block.Block
import org.checkerframework.dataflow.cfg.block.ConditionalBlock
import org.checkerframework.dataflow.cfg.block.RegularBlock
import org.checkerframework.dataflow.cfg.block.SpecialBlock
import org.checkerframework.dataflow.cfg.node.ConditionalNotNode
import org.checkerframework.dataflow.cfg.node.Node
import org.checkerframework.dataflow.cfg.node.ReturnNode
import org.checkerframework.framework.flow.CFAbstractAnalysis
import org.checkerframework.framework.flow.CFAbstractValue
import org.checkerframework.javacutil.Pair
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.VariableElement
import javax.lang.model.type.TypeMirror

class MungoAnalysis(checker: MungoChecker, factory: MungoAnnotatedTypeFactory, fieldValues: List<Pair<VariableElement, MungoValue>>) : CFAbstractAnalysis<MungoValue, MungoStore, MungoTransfer>(checker, factory, fieldValues) {

  val c = checker
  val f = factory
  val utils get() = c.utils
  var inPublicMethodAnalysis: Boolean = false
  var creatingInitialStore: Boolean = false

  override fun createEmptyStore(sequentialSemantics: Boolean): MungoStore {
    return MungoStore(this, sequentialSemantics)
  }

  override fun createCopiedStore(s: MungoStore?): MungoStore {
    // Workaround null value in CFAbstractTransfer#initialStore in the case AST is a lambda
    if (s == null) return createEmptyStore(transferFunction?.usesSequentialSemantics() ?: false)
    return MungoStore(s)
  }

  override fun createAbstractValue(annotations: Set<AnnotationMirror>, underlyingType: TypeMirror): MungoValue? {
    return if (!CFAbstractValue.validateSet(annotations, underlyingType, qualifierHierarchy)) {
      null
    } else MungoValue(this, annotations, underlyingType)
  }

  fun nextIsConditional(node: Node): Boolean {
    val block = node.block
    if (block is RegularBlock) {
      val succ = block.successor
      if (succ is ConditionalBlock) {
        return block.contents.last() === node
      }
    }
    return false
  }

  private fun shouldEachToEach(node: Node?, succ: Block): Boolean {
    return when (succ) {
      is ConditionalBlock -> true
      is SpecialBlock -> succ.specialType == SpecialBlock.SpecialBlockType.EXIT
      is RegularBlock -> shouldEachToEach(node, succ.contents.firstOrNull())
      else -> false
    }
  }

  private fun shouldEachToEach(node: Node?, after: Node?): Boolean {
    return when (after) {
      is ReturnNode -> after.result === node
      is ConditionalNotNode -> after.operand === node
      else -> false
    }
  }

  // We also need to control the propagation for nodes inside RegularBlock's contents
  override fun callTransferFunction(node: Node, input: TransferInput<MungoValue, MungoStore>): TransferResult<MungoValue, MungoStore> {
    val block = node.block
    if (block is RegularBlock) {
      val idx = block.contents.indexOf(node)
      val prevIdx = idx - 1
      if (prevIdx >= 0) {
        val prev = block.contents[prevIdx]
        if (!shouldEachToEach(prev, node)) {
          return super.callTransferFunction(node, TransferInput(input.node, this, input.regularStore))
        }
      }
    }
    return super.callTransferFunction(node, input)
  }

  override fun propagateStoresTo(
    succ: Block,
    node: Node?,
    currentInput: TransferInput<MungoValue, MungoStore>,
    flowRule: FlowRule,
    addToWorklistAgain: Boolean
  ) {
    when (flowRule) {
      FlowRule.EACH_TO_EACH -> if (currentInput.containsTwoStores() && shouldEachToEach(node, succ)) {
        addStoreBefore(
          succ,
          node,
          currentInput.thenStore,
          Store.Kind.THEN,
          addToWorklistAgain)
        addStoreBefore(
          succ,
          node,
          currentInput.elseStore,
          Store.Kind.ELSE,
          addToWorklistAgain)
      } else {
        addStoreBefore(
          succ,
          node,
          currentInput.regularStore,
          Store.Kind.BOTH,
          addToWorklistAgain)
      }
      FlowRule.THEN_TO_BOTH -> addStoreBefore(
        succ,
        node,
        currentInput.thenStore,
        Store.Kind.BOTH,
        addToWorklistAgain)
      FlowRule.ELSE_TO_BOTH -> addStoreBefore(
        succ,
        node,
        currentInput.elseStore,
        Store.Kind.BOTH,
        addToWorklistAgain)
      FlowRule.THEN_TO_THEN -> addStoreBefore(
        succ,
        node,
        currentInput.thenStore,
        Store.Kind.THEN,
        addToWorklistAgain)
      FlowRule.ELSE_TO_ELSE -> addStoreBefore(
        succ,
        node,
        currentInput.elseStore,
        Store.Kind.ELSE,
        addToWorklistAgain)
    }
  }
}
