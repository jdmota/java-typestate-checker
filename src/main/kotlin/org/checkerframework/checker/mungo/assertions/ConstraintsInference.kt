package org.checkerframework.checker.mungo.assertions

import org.checkerframework.dataflow.cfg.node.*

class ConstraintsInference : AbstractNodeVisitor<Assertion, Assertion>() {

  //private val Assertion() = InferenceResult(Assertion(), Assertion())

  override fun visitNode(n: Node?, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitThisLiteral(n: ThisLiteralNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitTernaryExpression(n: TernaryExpressionNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitConditionalNot(n: ConditionalNotNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitBooleanLiteral(n: BooleanLiteralNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitEqualTo(n: EqualToNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitNotEqual(n: NotEqualNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitAssignment(n: AssignmentNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitReturn(n: ReturnNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitMethodAccess(n: MethodAccessNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitLambdaResultExpression(n: LambdaResultExpressionNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitStringConcatenateAssignment(n: StringConcatenateAssignmentNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitObjectCreation(node: ObjectCreationNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitMethodInvocation(n: MethodInvocationNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitCase(n: CaseNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitInstanceOf(n: InstanceOfNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitVariableDeclaration(n: VariableDeclarationNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitNarrowingConversion(n: NarrowingConversionNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitWideningConversion(n: WideningConversionNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitStringConversion(n: StringConversionNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitLocalVariable(n: LocalVariableNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitFieldAccess(n: FieldAccessNode, preCondition: Assertion): Assertion {
    return Assertion()
  }

  override fun visitTypeCast(n: TypeCastNode, preCondition: Assertion): Assertion {
    return Assertion()
  }
}
