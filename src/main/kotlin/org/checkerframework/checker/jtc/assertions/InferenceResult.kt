package org.checkerframework.checker.jtc.assertions

import com.microsoft.z3.*
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

  abstract fun equals(assertion: SymbolicAssertion, a: Reference, b: Reference): String

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

  override fun equals(assertion: SymbolicAssertion, a: Reference, b: Reference): String {
    return model1.eval(setup.mkEquals(assertion, a, b), false).toString()
  }

}

class Solution(setup: ConstraintsSetup, model1: Model, model2: Model, val simplifier: Simplifier?) : SomeSolution(setup, model1, model2) {

  override fun get(x: SymbolicFraction): String {
    val fraction = Make.S.fraction(x)
    val maybeResult = simplifier?.get(fraction) ?: fraction
    if (maybeResult is TinyReal) {
      return maybeResult.toString()
    }
    return model1.eval(maybeResult.toZ3(setup), true).toString()
  }

  override fun get(x: SymbolicType): String {
    val type = Make.S.type(x)
    val maybeResult = simplifier?.get(type) ?: type
    if (maybeResult is TinyJTCType) {
      return maybeResult.toString()
    }
    return setup.labelToType(model2!!.eval(maybeResult.toZ3(setup), true).toString()).format()
  }

  override fun equals(assertion: SymbolicAssertion, a: Reference, b: Reference): String {
    val equals = Make.S.equals(assertion, a, b)
    val maybeResult = simplifier?.get(equals) ?: equals
    if (maybeResult is TinyReal) {
      return maybeResult.toString()
    }
    return model1.eval(maybeResult.toZ3(setup), false).toString()
  }

}
