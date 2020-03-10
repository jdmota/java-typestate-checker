package org.checkerframework.checker.mungo;

import org.checkerframework.checker.mungo.internal.MungoUtils;
import org.checkerframework.dataflow.analysis.FlowExpressions;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode;
import org.checkerframework.framework.flow.*;

import java.util.Set;

public class MungoTransfer extends CFTransfer {
  public MungoTransfer(CFAnalysis analysis) {
    super(analysis);
  }

  @Override
  public TransferResult<CFValue, CFStore> visitMethodInvocation(MethodInvocationNode n, TransferInput<CFValue, CFStore> in) {
    TransferResult<CFValue, CFStore> result = super.visitMethodInvocation(n, in);
    Node methodReceiver = n.getTarget().getReceiver();

    FlowExpressions.Receiver receiver = FlowExpressions.internalReprOf(analysis.getTypeFactory(), methodReceiver);

    CFStore thenStore = result.getThenStore();
    CFValue value = thenStore.getValue(receiver);
    if (value != null) {
      Set<String> states = MungoUtils.getStatesFromAnnotations(value.getAnnotations());
      System.out.println(value + " " + states);
      thenStore.replaceValue(receiver, new CFValue(analysis, value.getAnnotations(), value.getUnderlyingType()));
    }
    // TODO

    // return new ConditionalTransferResult<>(result.getResultValue(), thenStore, elseStore);
    return result;
  }

  @Override
  public TransferResult<CFValue, CFStore> visitObjectCreation(ObjectCreationNode n, TransferInput<CFValue, CFStore> in) {
    TransferResult<CFValue, CFStore> result = super.visitObjectCreation(n, in);
    // System.out.println("new " + n + " " + result);
    return result;
  }
}
