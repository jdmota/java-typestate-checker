package org.checkerframework.checker.mungo;

import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode;
import org.checkerframework.framework.flow.*;

public class MungoTransfer extends CFTransfer {
  public MungoTransfer(CFAnalysis analysis) {
    super(analysis);
  }

  /*@Override
  public TransferResult<CFValue, CFStore> visitMethodInvocation(MethodInvocationNode n, TransferInput<CFValue, CFStore> in) {
    //System.out.println("mi " + n);
    return super.visitMethodInvocation(n, in);
  }

  @Override
  public TransferResult<CFValue, CFStore> visitClassDeclaration(ClassDeclarationNode n, TransferInput<CFValue, CFStore> in) {
    System.out.println("TRANSFER class decl " + n);
    TransferResult<CFValue, CFStore> result = super.visitClassDeclaration(n, in);
    System.out.println(result);
    return result;
  }*/

  @Override
  public TransferResult<CFValue, CFStore> visitObjectCreation(ObjectCreationNode n, TransferInput<CFValue, CFStore> in) {
    TransferResult<CFValue, CFStore> result = super.visitObjectCreation(n, in);
    System.out.println(result);
    return result;
  }
}
