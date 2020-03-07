package org.checkerframework.checker.mungo;

import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.framework.flow.*;

public class MungoTransfer extends CFTransfer {
  public MungoTransfer(CFAnalysis analysis) {
    super(analysis);
  }

  @Override
  public TransferResult<CFValue, CFStore> visitMethodInvocation(MethodInvocationNode n, TransferInput<CFValue, CFStore> in) {
    return super.visitMethodInvocation(n, in);
  }
}
