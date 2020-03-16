package org.checkerframework.checker.mungo.typecheck

import com.sun.source.tree.MethodInvocationTree
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.common.basetype.BaseTypeVisitor
import org.checkerframework.javacutil.TreeUtils
import javax.lang.model.element.ElementKind

class MungoVisitor(checker: MungoChecker) : BaseTypeVisitor<MungoAnnotatedTypeFactory>(checker) {

  private val c = checker

  override fun createTypeFactory(): MungoAnnotatedTypeFactory {
    // Pass "checker" and not "c" because "c" is initialized after "super()" and "createTypeFactory()"...
    return MungoAnnotatedTypeFactory(checker as MungoChecker)
  }

  // TODO visit all annotations to make sure @MungoTypestate only appears in class/interfaces??
  // TODO what if another class points to the same protocol file?? error? or fine? avoid duplicate processing

  /*override fun checkMethodInvocability(method: AnnotatedTypeMirror.AnnotatedExecutableType, node: MethodInvocationTree) {
    super.checkMethodInvocability(method, node)
  }*/

  override fun visitMethodInvocation(node: MethodInvocationTree, p: Void?): Void? {
    val element = TreeUtils.elementFromUse(node)
    if (element is Symbol.MethodSymbol && element.getKind() == ElementKind.METHOD) {
      val receiverType = typeFactory.getReceiverType(node)
      if (receiverType != null) {
        MungoTypecheck.check(c.utils, visitorState.path, receiverType.annotations, node, element)
      }
    }
    return super.visitMethodInvocation(node, p)
  }
}
