package org.checkerframework.checker.mungo.assertions

import org.checkerframework.dataflow.cfg.node.*

class ConstraintsInference : AbstractNodeVisitor<Void?, Void?>() {

  override fun visitNode(n: Node?, p: Void?): Void? {
    return null
  }

  override fun visitThisLiteral(n: ThisLiteralNode, res: Void?): Void? {
    return null
  }

  override fun visitTernaryExpression(n: TernaryExpressionNode, res: Void?): Void? {
    return null
  }

  override fun visitConditionalNot(n: ConditionalNotNode, res: Void?): Void? {
    return null
  }

  override fun visitBooleanLiteral(n: BooleanLiteralNode, res: Void?): Void? {
    return null
  }

  override fun visitEqualTo(n: EqualToNode, res: Void?): Void? {
    return null
  }

  override fun visitNotEqual(n: NotEqualNode, res: Void?): Void? {
    return null
  }

  override fun visitAssignment(n: AssignmentNode, result: Void?): Void? {
    return null
  }

  override fun visitReturn(n: ReturnNode, result: Void?): Void? {
    return null
  }

  override fun visitMethodAccess(n: MethodAccessNode, result: Void?): Void? {
    return null
  }

  override fun visitLambdaResultExpression(n: LambdaResultExpressionNode, input: Void?): Void? {
    return null
  }

  override fun visitStringConcatenateAssignment(n: StringConcatenateAssignmentNode, res: Void?): Void? {
    return null
  }

  override fun visitObjectCreation(node: ObjectCreationNode, result: Void?): Void? {
    return null
  }

  override fun visitMethodInvocation(n: MethodInvocationNode, result: Void?): Void? {
    return null
  }

  override fun visitCase(n: CaseNode, result: Void?): Void? {
    return null
  }

  override fun visitInstanceOf(n: InstanceOfNode, result: Void?): Void? {
    return null
  }

  override fun visitVariableDeclaration(n: VariableDeclarationNode, result: Void?): Void? {
    return null
  }

  override fun visitNarrowingConversion(n: NarrowingConversionNode, result: Void?): Void? {
    return null
  }

  override fun visitWideningConversion(n: WideningConversionNode, result: Void?): Void? {
    return null
  }

  override fun visitStringConversion(n: StringConversionNode, result: Void?): Void? {
    return null
  }

  override fun visitLocalVariable(n: LocalVariableNode, result: Void?): Void? {
    return null
  }

  override fun visitFieldAccess(n: FieldAccessNode, result: Void?): Void? {
    return null
  }

  override fun visitTypeCast(n: TypeCastNode, result: Void?): Void? {
    return null
  }
}
