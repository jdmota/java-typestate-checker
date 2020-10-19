package org.checkerframework.checker.mungo.assertions

import org.checkerframework.checker.mungo.analysis.Reference
import org.checkerframework.checker.mungo.analysis.getReference
import org.checkerframework.dataflow.cfg.node.*

class ConstraintsInference(private val inferrer: Inferrer, private val constraints: Constraints) : AbstractNodeVisitor<Void?, NodeAssertions>() {

  private fun getRef(n: Node) = getReference(n) ?: error("No reference for $n")

  private fun read(ref: Reference, assertions: NodeAssertions) {
    constraints.notZero(assertions.preThen.getAccess(ref))
    if (assertions.preThen !== assertions.preElse) {
      constraints.notZero(assertions.preElse.getAccess(ref))
    }
  }

  private fun write(ref: Reference, assertions: NodeAssertions) {
    constraints.one(assertions.preThen.getAccess(ref))
    if (assertions.preThen !== assertions.preElse) {
      constraints.one(assertions.preElse.getAccess(ref))
    }
  }

  private fun noSideEffects(result: NodeAssertions) {
    constraints.eq(result.preThen, result.postThen)
    if (result.preThen !== result.preElse || result.postThen !== result.postElse) {
      constraints.eq(result.preElse, result.postElse)
    }
  }

  override fun visitThisLiteral(n: ThisLiteralNode, result: NodeAssertions): Void? {
    read(getRef(n), result)
    noSideEffects(result)
    return null
  }

  override fun visitLocalVariable(n: LocalVariableNode, result: NodeAssertions): Void? {
    read(getRef(n), result)
    noSideEffects(result)
    return null
  }

  override fun visitFieldAccess(n: FieldAccessNode, result: NodeAssertions): Void? {
    read(getRef(n), result)
    noSideEffects(result)
    return null
  }

  override fun visitVariableDeclaration(n: VariableDeclarationNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitAssignment(n: AssignmentNode, result: NodeAssertions): Void? {
    write(getRef(n.target), result)
    return null
  }

  override fun visitObjectCreation(node: ObjectCreationNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitMethodAccess(n: MethodAccessNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitMethodInvocation(n: MethodInvocationNode, result: NodeAssertions): Void? {
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

  override fun visitBooleanLiteral(n: BooleanLiteralNode, result: NodeAssertions): Void? {
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

  override fun visitNode(n: Node?, result: NodeAssertions): Void? {
    return null
  }
}
