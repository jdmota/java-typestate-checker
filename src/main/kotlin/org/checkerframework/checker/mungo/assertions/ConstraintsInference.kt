package org.checkerframework.checker.mungo.assertions

import org.checkerframework.dataflow.cfg.node.*

class ConstraintsInference : AbstractNodeVisitor<Void?, MutableAnalyzerResultWithValue>() {

  override fun visitNode(n: Node?, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitThisLiteral(n: ThisLiteralNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitTernaryExpression(n: TernaryExpressionNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitConditionalNot(n: ConditionalNotNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitBooleanLiteral(n: BooleanLiteralNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitEqualTo(n: EqualToNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitNotEqual(n: NotEqualNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitAssignment(n: AssignmentNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitReturn(n: ReturnNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitMethodAccess(n: MethodAccessNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitLambdaResultExpression(n: LambdaResultExpressionNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitStringConcatenateAssignment(n: StringConcatenateAssignmentNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitObjectCreation(node: ObjectCreationNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitMethodInvocation(n: MethodInvocationNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitCase(n: CaseNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitInstanceOf(n: InstanceOfNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitVariableDeclaration(n: VariableDeclarationNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitNarrowingConversion(n: NarrowingConversionNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitWideningConversion(n: WideningConversionNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitStringConversion(n: StringConversionNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitLocalVariable(n: LocalVariableNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitFieldAccess(n: FieldAccessNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }

  override fun visitTypeCast(n: TypeCastNode, result: MutableAnalyzerResultWithValue): Void? {
    return null
  }
}
