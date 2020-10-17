package org.checkerframework.checker.mungo.assertions

import org.checkerframework.dataflow.cfg.node.*

class ConstraintsInference : AbstractNodeVisitor<Void?, NodeAssertions>() {

  override fun visitNode(n: Node?, result: NodeAssertions): Void? {
    return null
  }

  override fun visitThisLiteral(n: ThisLiteralNode, result: NodeAssertions): Void? {
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

  override fun visitAssignment(n: AssignmentNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitReturn(n: ReturnNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitMethodAccess(n: MethodAccessNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitLambdaResultExpression(n: LambdaResultExpressionNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitStringConcatenateAssignment(n: StringConcatenateAssignmentNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitObjectCreation(node: ObjectCreationNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitMethodInvocation(n: MethodInvocationNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitCase(n: CaseNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitInstanceOf(n: InstanceOfNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitVariableDeclaration(n: VariableDeclarationNode, result: NodeAssertions): Void? {
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

  override fun visitLocalVariable(n: LocalVariableNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitFieldAccess(n: FieldAccessNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitTypeCast(n: TypeCastNode, result: NodeAssertions): Void? {
    return null
  }
}
