package org.checkerframework.checker.mungo.analysis

import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.code.Symtab
import com.sun.tools.javac.code.Type
import com.sun.tools.javac.processing.JavacProcessingEnvironment
import com.sun.tools.javac.tree.TreeMaker
import com.sun.tools.javac.util.Names
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.typestate.TypestateProcessor
import org.checkerframework.checker.mungo.typestate.ast.Position
import org.checkerframework.checker.mungo.typestate.ast.TIdNode
import org.checkerframework.checker.mungo.typestate.ast.TMethodNode
import org.checkerframework.checker.mungo.utils.MungoUtils.Companion.getInfoFromAnnotations
import org.checkerframework.dataflow.analysis.FlowExpressions
import org.checkerframework.dataflow.analysis.TransferInput
import org.checkerframework.dataflow.analysis.TransferResult
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode
import org.checkerframework.framework.flow.CFAbstractTransfer
import java.util.*

class MungoTransfer(checker: MungoChecker, analysis: MungoAnalysis) : CFAbstractTransfer<MungoValue, MungoStore, MungoTransfer>(analysis) {

  private val c = checker;

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

    // val maker = TreeMaker.instance((c.processingEnvironment as JavacProcessingEnvironment).context)
    val names = Names.instance((c.processingEnvironment as JavacProcessingEnvironment).context)
    val symtab = Symtab.instance((c.processingEnvironment as JavacProcessingEnvironment).context)

    val newMethod = TypestateProcessor.methodNodeToMethodSymbol(
      symtab,
      names,
      TMethodNode(Position.nil, "boolean", "hasNext", LinkedList(), TIdNode(Position.nil, "dest")),
      method.owner
    )

    println(method.type)
    println(newMethod.type)
    println(method.type.equals(newMethod.type))

    //val methodExec = TreeUtils.elementFromDeclaration(newMethodTree);
    //println(newMethodTree)
    //println(methodExec)
    //println(methodExec::class.java)

    val thenStore = result.thenStore
    val value = thenStore.getValue(receiver)
    if (value != null) {
      val info = getInfoFromAnnotations(value.annotations)
      println("$value $info")
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
