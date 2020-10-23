package org.checkerframework.checker.mungo.assertions

import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.checker.mungo.typecheck.MungoObjectType
import org.checkerframework.checker.mungo.typecheck.MungoType
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
        notNull(getRefForSure(node.receiver), assertions)
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
        notNull(getRefForSure(node.receiver), assertions)
        read(node.receiver, assertions)
      }
    }

    private fun notNull(ref: Reference, assertions: NodeAssertions) {
      type(ref, assertions, MungoObjectType.SINGLETON)
    }

    fun type(ref: Reference, assertions: NodeAssertions, type: MungoType) {
      constraints.subtype(assertions.preThen.getType(ref), type)
      if (assertions.preThen !== assertions.preElse) {
        constraints.subtype(assertions.preThen.getType(ref), type)
      }
    }
  }

  private val ensures = object {
    fun newVar(info: SymbolicInfo) {
      constraints.one(info.fraction)
      constraints.one(info.packFraction)
      constraints.nullType(info.type)
    }

    fun newVar(ref: Reference, assertions: NodeAssertions) {
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

    fun type(ref: Reference, assertions: NodeAssertions, type: MungoType) {
      constraints.subtype(type, assertions.postThen.getType(ref))
      if (assertions.postThen !== assertions.preElse) {
        constraints.subtype(type, assertions.postThen.getType(ref))
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
    val ref = getRefForSure(n)
    ensures.newVar(ref, result)
    ensures.onlySideEffect(result, setOf(ref))
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
      // TODO move permissions of fields
      constraints.same(preTargetInfo.packFraction, postOldVarInfo.packFraction)
      constraints.same(preTargetInfo.type, postOldVarInfo.type)

      // Equality
      // TODO equality of fields as well
      if (exprRef == null) {
        constraints.equality(postTargetInfo, postExprInfo, preExprInfo.packFraction, preExprInfo.type)
      } else {
        constraints.equality(post, targetRef, exprRef, preExprInfo.packFraction, preExprInfo.type)
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

    assign(targetRef, n.expression, oldRef, result)
    return null
  }

  override fun visitObjectCreation(node: ObjectCreationNode, result: NodeAssertions): Void? {
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

    val pre = inferrer.getMethodPre(method)
    val (postThen, postElse) = inferrer.getMethodPost(method)

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
    return null
  }

  override fun visitBooleanLiteral(n: BooleanLiteralNode, result: NodeAssertions): Void? {
    return super.visitBooleanLiteral(n, result)
  }

  override fun visitNode(n: Node?, result: NodeAssertions): Void? {
    if (n is ValueLiteralNode) {
      ensures.noSideEffects(result)
    }
    return null
  }
}
