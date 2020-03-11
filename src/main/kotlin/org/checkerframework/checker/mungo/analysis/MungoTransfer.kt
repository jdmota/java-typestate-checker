package org.checkerframework.checker.mungo.analysis

import org.checkerframework.checker.mungo.utils.MungoUtils.Companion.getInfoFromAnnotations
import org.checkerframework.dataflow.analysis.FlowExpressions
import org.checkerframework.dataflow.analysis.TransferInput
import org.checkerframework.dataflow.analysis.TransferResult
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode
import org.checkerframework.framework.flow.CFAbstractTransfer

class MungoTransfer(analysis: MungoAnalysis) : CFAbstractTransfer<MungoValue, MungoStore, MungoTransfer>(analysis) {
  override fun visitMethodInvocation(n: MethodInvocationNode, input: TransferInput<MungoValue, MungoStore>): TransferResult<MungoValue, MungoStore> {
    val result = super.visitMethodInvocation(n, input)
    val methodReceiver = n.target.receiver
    val receiver = FlowExpressions.internalReprOf(analysis.typeFactory, methodReceiver)
    val thenStore = result.thenStore
    val value = thenStore.getValue(receiver)
    if (value != null) {
      val info = getInfoFromAnnotations(value.annotations)
      println("$value $info")
      thenStore.replaceValue(receiver, analysis.createAbstractValue(value.annotations, value.underlyingType))
    }
    // TODO

    // return new ConditionalTransferResult<>(result.getResultValue(), thenStore, elseStore);
    return result
  }

  override fun visitObjectCreation(n: ObjectCreationNode, input: TransferInput<MungoValue, MungoStore>): TransferResult<MungoValue, MungoStore> {
    // System.out.println("new " + n + " " + result);
    return super.visitObjectCreation(n, input)
  }
}
