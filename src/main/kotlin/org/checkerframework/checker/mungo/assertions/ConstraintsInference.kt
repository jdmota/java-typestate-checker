package org.checkerframework.checker.mungo.assertions

import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.checker.mungo.typecheck.*
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.dataflow.cfg.node.*
import javax.lang.model.element.ElementKind

class ConstraintsInference(private val inferrer: Inferrer, private val constraints: Constraints) : AbstractNodeVisitor<Void?, NodeAssertions>() {

  private fun getRef(n: Node) = inferrer.getReference(n)
  private fun getRefForSure(n: Node) = inferrer.getReference(n) ?: error("No reference for $n")
  private fun getInfo(n: Node, a: SymbolicAssertion) = inferrer.getInfo(n, a)

  private val require = object {
    fun read(node: Node, assertions: NodeAssertions) {
      val thenInfo = inferrer.getInfo(node, assertions.preThen)
      val elseInfo = inferrer.getInfo(node, assertions.preElse)

      constraints.notZero(thenInfo.fraction)
      if (thenInfo !== elseInfo) {
        constraints.notZero(elseInfo.fraction)
      }

      if (node is FieldAccessNode) {
        notNull(node.receiver, assertions)
        read(node.receiver, assertions)
      }
    }

    fun write(node: Node, assertions: NodeAssertions) {
      val thenInfo = inferrer.getInfo(node, assertions.preThen)
      val elseInfo = inferrer.getInfo(node, assertions.preElse)

      constraints.one(thenInfo.fraction)
      if (thenInfo !== elseInfo) {
        constraints.one(elseInfo.fraction)
      }

      if (node is FieldAccessNode) {
        notNull(node.receiver, assertions)
        read(node.receiver, assertions)
      }
    }

    private fun notNull(node: Node, assertions: NodeAssertions) {
      type(node, assertions, MungoObjectType.SINGLETON)
    }

    fun type(node: Node, assertions: NodeAssertions, type: MungoType) {
      val thenInfo = inferrer.getInfo(node, assertions.preThen)
      val elseInfo = inferrer.getInfo(node, assertions.preElse)

      constraints.subtype(thenInfo.type, type)
      if (thenInfo !== elseInfo) {
        constraints.subtype(elseInfo.type, type)
      }
    }
  }

  private val ensures = object {
    fun newVar(info: SymbolicInfo) {
      constraints.one(info.fraction)
      constraints.one(info.packFraction)
      constraints.nullType(info.type)
    }

    fun newVar(n: VariableDeclarationNode, assertions: NodeAssertions) {
      val ref = getRefForSure(n)
      newVar(assertions.postThen[ref])
      if (assertions.postThen !== assertions.postElse) {
        newVar(assertions.postElse[ref])
      }
    }

    fun noSideEffects(result: NodeAssertions) {
      onlySideEffect(result, emptySet())
    }

    fun onlySideEffect(result: NodeAssertions, except: Set<Reference>) {
      constraints.onlyEffects(result.preThen, result.postThen, except)
      if (result.preThen !== result.preElse || result.postThen !== result.postElse) {
        constraints.onlyEffects(result.preElse, result.postElse, except)
      }
    }

    fun newValue(node: Node, assertions: NodeAssertions, type: MungoType) {
      // TODO full permission to fields...

      val thenInfo = inferrer.getInfo(node, assertions.postThen)
      val elseInfo = inferrer.getInfo(node, assertions.postElse)

      constraints.subtype(type, thenInfo.type)
      constraints.one(thenInfo.packFraction)
      if (thenInfo !== elseInfo) {
        constraints.subtype(type, elseInfo.type)
        constraints.one(elseInfo.packFraction)
      }
    }
  }

  fun visitInitialAssertion(ast: UnderlyingAST, pre: SymbolicAssertion) {
    pre.forEach { ref, info ->
      when (ref) {
        is LocalVariable -> {
          if (ref.element.getKind() == ElementKind.PARAMETER) {
            constraints.one(info.fraction)
          }
        }
        is ThisReference -> {
          constraints.one(info.fraction)
          constraints.subtype(MungoObjectType.SINGLETON, info.type)
        }
        is FieldAccess -> {
        }
        is ClassName -> {
        }
        is ReturnSpecialVar -> {
          ensures.newVar(info)
        }
        is OldSpecialVar -> {
          ensures.newVar(info)
        }
      }
    }

    // TODO What about lambdas???
    for ((a, b) in pre.skeleton.equalities) {
      constraints.notEquality(pre, a, b)
    }
  }

  override fun visitThisLiteral(n: ThisLiteralNode, result: NodeAssertions): Void? {
    require.read(n, result)
    ensures.noSideEffects(result)
    return null
  }

  override fun visitLocalVariable(n: LocalVariableNode, result: NodeAssertions): Void? {
    require.read(n, result)
    ensures.noSideEffects(result)
    return null
  }

  override fun visitFieldAccess(n: FieldAccessNode, result: NodeAssertions): Void? {
    require.read(n, result)
    ensures.noSideEffects(result)
    return null
  }

  override fun visitMethodAccess(n: MethodAccessNode, result: NodeAssertions): Void? {
    require.read(n.receiver, result)
    ensures.noSideEffects(result)
    return null
  }

  override fun visitVariableDeclaration(n: VariableDeclarationNode, result: NodeAssertions): Void? {
    ensures.newVar(n, result)
    ensures.onlySideEffect(result, setOf(getRefForSure(n)))
    return null
  }

  private fun assign(targetRef: Reference, expr: Node, oldRef: Reference, result: NodeAssertions) {
    val exprRef = getRef(expr)

    fun helper(pre: SymbolicAssertion, post: SymbolicAssertion) {
      val preTargetInfo = pre[targetRef]
      val preExprInfo = getInfo(expr, pre)
      val postTargetInfo = post[targetRef]
      val postExprInfo = getInfo(expr, post)
      val postOldVarInfo = post[oldRef]

      // Permission to the target and expression remain the same
      constraints.same(preTargetInfo.fraction, postTargetInfo.fraction)
      constraints.same(preExprInfo.fraction, postExprInfo.fraction)

      // Move permissions and type of the old object to the ghost variable
      constraints.transfer(target = postOldVarInfo, null, data = preTargetInfo)

      // Equality
      if (exprRef == null) {
        constraints.transfer(target = postTargetInfo, expr = postExprInfo, data = preExprInfo)
      } else {
        constraints.equality(assertion = post, target = targetRef, expr = exprRef, data = preExprInfo)
      }
    }

    helper(result.preThen, result.postThen)
    if (result.preThen !== result.preElse || result.postThen !== result.postElse) {
      helper(result.preElse, result.postElse)
    }

    if (exprRef == null) {
      ensures.onlySideEffect(result, setOf(targetRef))
    } else {
      ensures.onlySideEffect(result, setOf(targetRef, exprRef))
    }
  }

  override fun visitAssignment(n: AssignmentNode, result: NodeAssertions): Void? {
    val targetRef = getRefForSure(n.target)
    val oldRef = getRefForSure(n)

    require.write(n.target, result)
    require.read(n.expression, result)

    // TODO handle primitives

    assign(targetRef, n.expression, oldRef, result)
    return null
  }

  override fun visitObjectCreation(node: ObjectCreationNode, result: NodeAssertions): Void? {
    val newType = MungoTypecheck.objectCreation(inferrer.utils, node.type)
    ensures.newValue(node, result, newType)
    return null
  }

  /*
  Think of method calls like:

  d = method(a, b, c)

  as:

  #arg0 = a
  #arg1 = b
  #arg2 = c
  method()
  d = #ret
  */
  override fun visitMethodInvocation(n: MethodInvocationNode, result: NodeAssertions): Void? {
    require.read(n.target.receiver, result)

    val method = n.target.method as Symbol.MethodSymbol
    val argExprs = n.arguments

    val parameters = inferrer.locationsGatherer.getParameterLocations(method)

    println(method)
    println(argExprs)
    println(parameters)
    println()

    // TODO handle methods for which we do not have the code...
    val pre = inferrer.getMethodPre(method) ?: return null
    val (postThen, postElse) = inferrer.getMethodPost(method) ?: return null

    val graph = inferrer.utils.classUtils.visitClassTypeMirror(n.target.receiver.type)
    if (graph == null) {
      // TODO same type
    } else {
      val states = MungoTypecheck.available(inferrer.utils, graph, method)
      val union = MungoUnionType.create(states)
      require.type(n.target.receiver, result, union)
    }

    // Transfer information about the return value
    constraints.transfer(target = getInfo(n, result.postThen), null, data = postThen[ReturnSpecialVar(n.type)])
    if (result.postThen !== result.postElse || postThen !== postElse) {
      constraints.transfer(target = getInfo(n, result.postElse), null, data = postElse[ReturnSpecialVar(n.type)])
    }
    return null
  }

  override fun visitReturn(n: ReturnNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitTernaryExpression(n: TernaryExpressionNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitConditionalNot(n: ConditionalNotNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitEqualTo(n: EqualToNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitNotEqual(n: NotEqualNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitLambdaResultExpression(n: LambdaResultExpressionNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitStringConcatenateAssignment(n: StringConcatenateAssignmentNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitCase(n: CaseNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitInstanceOf(n: InstanceOfNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitNarrowingConversion(n: NarrowingConversionNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitWideningConversion(n: WideningConversionNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitStringConversion(n: StringConversionNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitTypeCast(n: TypeCastNode, result: NodeAssertions): Void? {
    ensures.noSideEffects(result)
    return null
  }

  override fun visitValueLiteral(n: ValueLiteralNode, result: NodeAssertions): Void? {
    ensures.noSideEffects(result)
    when (n) {
      is NullLiteralNode -> ensures.newValue(n, result, MungoNullType.SINGLETON)
      is StringLiteralNode -> ensures.newValue(n, result, MungoNoProtocolType.SINGLETON)
      else -> ensures.newValue(n, result, MungoPrimitiveType.SINGLETON)
    }
    return null
  }

  override fun visitNode(n: Node?, result: NodeAssertions): Void? {
    return null
  }
}
