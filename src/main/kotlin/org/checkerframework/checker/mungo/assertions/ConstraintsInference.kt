package org.checkerframework.checker.mungo.assertions

import org.checkerframework.dataflow.cfg.node.*

class ConstraintsInference : AbstractNodeVisitor<Void?, InferenceResult>() {

  override fun visitNode(n: Node?, result: InferenceResult): Void? {
    return null
  }

  override fun visitThisLiteral(n: ThisLiteralNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitTernaryExpression(n: TernaryExpressionNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitConditionalNot(n: ConditionalNotNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitBooleanLiteral(n: BooleanLiteralNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitEqualTo(n: EqualToNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitNotEqual(n: NotEqualNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitAssignment(n: AssignmentNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitReturn(n: ReturnNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitMethodAccess(n: MethodAccessNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitLambdaResultExpression(n: LambdaResultExpressionNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitStringConcatenateAssignment(n: StringConcatenateAssignmentNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitObjectCreation(node: ObjectCreationNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitMethodInvocation(n: MethodInvocationNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitCase(n: CaseNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitInstanceOf(n: InstanceOfNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitVariableDeclaration(n: VariableDeclarationNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitNarrowingConversion(n: NarrowingConversionNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitWideningConversion(n: WideningConversionNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitStringConversion(n: StringConversionNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitLocalVariable(n: LocalVariableNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitFieldAccess(n: FieldAccessNode, result: InferenceResult): Void? {
    return null
  }

  override fun visitTypeCast(n: TypeCastNode, result: InferenceResult): Void? {
    return null
  }
}
