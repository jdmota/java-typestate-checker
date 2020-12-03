package org.checkerframework.checker.jtc.assertions

import com.microsoft.z3.*
import org.checkerframework.checker.jtc.analysis.*
import org.checkerframework.dataflow.cfg.node.*

sealed class MiniInferenceResult
class MiniNoSolution(val unsatCore: Array<BoolExpr>) : MiniInferenceResult()
class MiniUnknownSolution(val reason: String?) : MiniInferenceResult()
class MiniSolution(val model: Model) : MiniInferenceResult()

sealed class InferenceResult

class NoSolution(val unsatCore: Array<BoolExpr>) : InferenceResult()

class UnknownSolution(val reason: String?) : InferenceResult()

sealed class SomeSolution(protected val setup: ConstraintsSetup, val model1: Model, val model2: Model?) : InferenceResult() {

  fun <E : Expr, T : TinyExpr<T, E>> eval(expr: T): E {
    val model = model2 ?: model1
    return model.eval(expr.toZ3(setup), false).simplify() as E
  }

  abstract fun get(x: SymbolicFraction): String

  abstract fun get(x: SymbolicType): String

  abstract fun equals(assertion: SymbolicAssertion, a: Reference, b: Reference): Expr

  fun skipRef(ref: Reference): Boolean {
    return when (ref) {
      is FieldAccess -> false
      is ThisReference -> false
      is ClassName -> true
      is LocalVariable -> false
      is ParameterVariable -> false
      is ReturnSpecialVar -> false
      is OldSpecialVar -> false
      is NodeRef -> when (ref.node) {
        is MethodInvocationNode -> false
        is ObjectCreationNode -> false
        else -> true
      }
      is UnknownRef -> true
      is OuterContextRef -> true
    }
  }

  fun skipNode(node: Node): Boolean {
    return when (node) {
      is AssignmentNode -> false
      is MethodInvocationNode -> false
      is ObjectCreationNode -> false
      is ThisLiteralNode -> true
      is FieldAccessNode -> true
      else -> true
    }
  }

}

class IncompleteSolution(setup: ConstraintsSetup, model: Model, val unsatCore: Array<BoolExpr>?) : SomeSolution(setup, model, null) {

  override fun get(x: SymbolicFraction): String = model1.eval(setup.mkFraction(x.z3Symbol()), true).toString()

  override fun get(x: SymbolicType): String = "Unknown"

  override fun equals(assertion: SymbolicAssertion, a: Reference, b: Reference): Expr {
    return model1.eval(setup.mkEquals(assertion, a, b), false)
  }

}

class Solution(setup: ConstraintsSetup, model1: Model, model2: Model) : SomeSolution(setup, model1, model2) {

  override fun get(x: SymbolicFraction): String = model1.eval(setup.mkFraction(x.z3Symbol()), true).toString()

  override fun get(x: SymbolicType): String = setup.labelToType(model2!!.eval(setup.mkType(x.z3Symbol()), true).toString()).format()

  override fun equals(assertion: SymbolicAssertion, a: Reference, b: Reference): Expr {
    return model1.eval(setup.mkEquals(assertion, a, b), false)
  }

}
