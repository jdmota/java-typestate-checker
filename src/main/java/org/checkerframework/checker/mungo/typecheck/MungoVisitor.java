package org.checkerframework.checker.mungo.typecheck;

import com.sun.source.tree.*;
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory;
import org.checkerframework.checker.mungo.MungoChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;

public class MungoVisitor extends BaseTypeVisitor<MungoAnnotatedTypeFactory> {
  public MungoVisitor(MungoChecker checker) {
    super(checker);
  }

  @Override
  protected MungoAnnotatedTypeFactory createTypeFactory() {
    return new MungoAnnotatedTypeFactory((MungoChecker) checker);
  }

  // TODO visit all annotations to make sure @MungoTypestate only appears in class/interfaces??
  // TODO what if another class points to the same protocol file?? error? or fine? avoid duplicate processing

  @Override
  public Void visitMethodInvocation(MethodInvocationTree node, Void p) {
    // TODO
    return super.visitMethodInvocation(node, p);
  }
}
