package org.checkerframework.checker.mungo.analysis;

import org.checkerframework.checker.mungo.typecheck.MungoTypeInfo;
import org.checkerframework.checker.mungo.utils.MungoUtils;
import org.checkerframework.dataflow.analysis.FlowExpressions;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode;
import org.checkerframework.framework.flow.*;

public class MungoTransfer extends CFAbstractTransfer<MungoValue, MungoStore, MungoTransfer> {
  public MungoTransfer(MungoAnalysis analysis) {
    super(analysis);
  }

  @Override
  public TransferResult<MungoValue, MungoStore> visitMethodInvocation(MethodInvocationNode n, TransferInput<MungoValue, MungoStore> in) {
    TransferResult<MungoValue, MungoStore> result = super.visitMethodInvocation(n, in);
    Node methodReceiver = n.getTarget().getReceiver();

    FlowExpressions.Receiver receiver = FlowExpressions.internalReprOf(analysis.getTypeFactory(), methodReceiver);

    MungoStore thenStore = result.getThenStore();
    MungoValue value = thenStore.getValue(receiver);
    if (value != null) {
      MungoTypeInfo info = MungoUtils.getInfoFromAnnotations(value.getAnnotations());
      System.out.println(value + " " + info);
      thenStore.replaceValue(receiver, analysis.createAbstractValue(value.getAnnotations(), value.getUnderlyingType()));
    }
    // TODO

    // return new ConditionalTransferResult<>(result.getResultValue(), thenStore, elseStore);
    return result;
  }

  @Override
  public TransferResult<MungoValue, MungoStore> visitObjectCreation(ObjectCreationNode n, TransferInput<MungoValue, MungoStore> in) {
    TransferResult<MungoValue, MungoStore> result = super.visitObjectCreation(n, in);
    // System.out.println("new " + n + " " + result);
    return result;
  }
}
