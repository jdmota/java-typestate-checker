package org.checkerframework.checker.mungo;

import org.checkerframework.checker.mungo.internal.MungoStore;
import org.checkerframework.checker.mungo.internal.MungoUtils;
import org.checkerframework.checker.mungo.internal.MungoValue;
import org.checkerframework.dataflow.analysis.FlowExpressions;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode;
import org.checkerframework.framework.flow.*;

import java.util.Set;

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
      Set<String> states = MungoUtils.getStatesFromAnnotations(value.getAnnotations());
      System.out.println(value + " " + states);
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
