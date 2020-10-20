package org.checkerframework.checker.mungo.assertions

import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.mungo.analysis.Reference
import org.checkerframework.checker.mungo.analysis.getReference
import org.checkerframework.dataflow.cfg.node.*

class ConstraintsInference(private val inferrer: Inferrer, private val constraints: Constraints) : AbstractNodeVisitor<Void?, NodeAssertions>() {

  private fun getRef(n: Node) = getReference(n) ?: error("No reference for $n")

  private val require = object {
    fun read(ref: Reference, assertions: NodeAssertions) {
      constraints.notZero(assertions.preThen.getAccess(ref))
      if (assertions.preThen !== assertions.preElse) {
        constraints.notZero(assertions.preElse.getAccess(ref))
      }
    }

    fun read(n: Node, result: NodeAssertions) {
      var curr: Node = n
      while (true) {
        read(getRef(curr), result)
        if (curr is FieldAccessNode) {
          curr = curr.receiver
        } else {
          break
        }
      }
    }

    fun write(ref: Reference, assertions: NodeAssertions) {
      constraints.one(assertions.preThen.getAccess(ref))
      if (assertions.preThen !== assertions.preElse) {
        constraints.one(assertions.preElse.getAccess(ref))
      }
    }
  }

  private val ensures = object {
    fun write(ref: Reference, assertions: NodeAssertions) {
      constraints.one(assertions.postThen.getAccess(ref))
      if (assertions.postThen !== assertions.postElse) {
        constraints.one(assertions.postElse.getAccess(ref))
      }
    }

    fun noSideEffects(result: NodeAssertions) {
      onlySideEffect(result, emptySet())
    }

    fun onlySideEffect(result: NodeAssertions, except: Set<Reference>) {
      constraints.implies(result.preThen, result.postThen, except)
      if (result.preThen !== result.preElse || result.postThen !== result.postElse) {
        constraints.implies(result.preElse, result.postElse, except)
      }
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
    val ref = getRef(n)
    ensures.write(ref, result)
    ensures.onlySideEffect(result, setOf(ref))
    return null
  }

  override fun visitAssignment(n: AssignmentNode, result: NodeAssertions): Void? {
    require.read(n.target, result)
    require.write(getRef(n.target), result)
    // TODO effects
    return null
  }

  override fun visitObjectCreation(node: ObjectCreationNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitMethodInvocation(n: MethodInvocationNode, result: NodeAssertions): Void? {
    require.read(n.target.receiver, result)

    // TODO handle varargs

    val method = n.target.method as Symbol.MethodSymbol
    val argExprs = n.arguments

    val parameters = inferrer.locationsGatherer.getParameterLocations(method)

    println(method)
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
