package org.checkerframework.checker.mungo.typecheck

import com.sun.source.tree.MethodInvocationTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory
import org.checkerframework.common.basetype.BaseTypeVisitor

class MungoVisitor(checker: MungoChecker) : BaseTypeVisitor<MungoAnnotatedTypeFactory>(checker) {
  override fun createTypeFactory(): MungoAnnotatedTypeFactory {
    return MungoAnnotatedTypeFactory(checker as MungoChecker)
  }

  // TODO visit all annotations to make sure @MungoTypestate only appears in class/interfaces??
  // TODO what if another class points to the same protocol file?? error? or fine? avoid duplicate processing

  override fun visitMethodInvocation(node: MethodInvocationTree, p: Void?): Void? {
    // TODO
    return super.visitMethodInvocation(node, p)
  }
}
