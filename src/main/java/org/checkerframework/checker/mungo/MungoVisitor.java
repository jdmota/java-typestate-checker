package org.checkerframework.checker.mungo;

import com.sun.source.tree.*;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.framework.source.Result;

public class MungoVisitor extends BaseTypeVisitor<MungoAnnotatedTypeFactory> {
  public MungoVisitor(BaseTypeChecker checker) {
    super(checker);
  }

  private void error(String message, Tree where) {
    checker.report(Result.failure(message), where);
  }

  // TODO visit all annotations to make sure @MungoTypestate only appears in class/interfaces??
  // TODO what if another class points to the same protocol file?? error? or fine? avoid duplicate processing

  @Override
  public Void visitMethodInvocation(MethodInvocationTree node, Void p) {
    // TODO
    return super.visitMethodInvocation(node, p);
  }
}
