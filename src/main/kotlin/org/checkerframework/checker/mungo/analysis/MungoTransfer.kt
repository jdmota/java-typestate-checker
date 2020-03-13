package org.checkerframework.checker.mungo.analysis

import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.dataflow.analysis.FlowExpressions
import org.checkerframework.dataflow.analysis.TransferInput
import org.checkerframework.dataflow.analysis.TransferResult
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode
import org.checkerframework.framework.flow.CFAbstractTransfer

class MungoTransfer(checker: MungoChecker, analysis: MungoAnalysis) : CFAbstractTransfer<MungoValue, MungoStore, MungoTransfer>(analysis) {

  private val c = checker

  override fun visitMethodInvocation(n: MethodInvocationNode, input: TransferInput<MungoValue, MungoStore>): TransferResult<MungoValue, MungoStore> {
    val result = super.visitMethodInvocation(n, input)
    val methodTarget = n.target
    val method = methodTarget.method as Symbol.MethodSymbol
    val methodReceiver = methodTarget.receiver
    val receiver = FlowExpressions.internalReprOf(analysis.typeFactory, methodReceiver)

    /*val methodName = method.name
    val methodParams = method.parameters
    val methodReturnType = method.returnType
    val methodThrownTypes = method.thrownTypes
    val methodTypeParameters = method.typeParameters
    val methodType = method.type as Type.MethodType
    val methodOwner = method.owner
    val methodTypeMethodClass = methodType.tsym*/

    val unit = n.treePath.compilationUnit as JCTree.JCCompilationUnit
    val sym = c.getUtils().resolve(n.treePath, "java.lang.Object")
    println(sym)
    println(sym::class.java)

    val sym2 = c.getUtils().resolve(n.treePath, "Object")
    println(sym2)
    println(sym2::class.java) // Expected to be ClassSymbol

    /*
    val newMethod = TypestateProcessor.methodNodeToMethodSymbol(
      symtab,
      names,
      TMethodNode(Position.nil, "boolean", "hasNext", LinkedList(), TIdNode(Position.nil, "dest")),
      method.owner
    )*/

    val thenStore = result.thenStore
    val value = thenStore.getValue(receiver)
    if (value != null) {
      val info = MungoUtils.getInfoFromAnnotations(value.annotations)
      println(value)
      if (info != null) {
        println(info.states)
      }
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
