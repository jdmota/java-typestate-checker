package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Expr
import com.microsoft.z3.Model
import org.checkerframework.checker.mungo.analysis.*

sealed class InferenceResult

class NoSolution(val unsatCore: Array<BoolExpr>) : InferenceResult()

class UnknownSolution(val reason: String?) : InferenceResult()

sealed class SomeSolution : InferenceResult() {

  abstract fun <T : Expr> eval(expr: T): T

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
      is NodeRef -> false
      is UnknownRef -> true
    }
  }

}

class IncompleteSolution(private val setup: ConstraintsSetup, val model: Model, val unsatCore: Array<BoolExpr>?) : SomeSolution() {

  override fun <T : Expr> eval(expr: T): T = model.eval(expr, false).simplify() as T

  override fun get(x: SymbolicFraction): String = model.eval(setup.mkFraction(x.z3Symbol()), true).toString()

  override fun get(x: SymbolicType): String = "Unknown"

  override fun equals(assertion: SymbolicAssertion, a: Reference, b: Reference): Expr {
    return model.eval(setup.mkEquals(assertion, a, b), false)
  }

}

class Solution(private val setup: ConstraintsSetup, val model: Model) : SomeSolution() {

  override fun <T : Expr> eval(expr: T): T = model.eval(expr, false).simplify() as T

  override fun get(x: SymbolicFraction): String = model.eval(setup.mkFraction(x.z3Symbol()), true).toString()

  override fun get(x: SymbolicType): String = setup.labelToType(model.eval(setup.mkType(x.z3Symbol()), true).toString()).format()

  override fun equals(assertion: SymbolicAssertion, a: Reference, b: Reference): Expr {
    return model.eval(setup.mkEquals(assertion, a, b), false)
  }

}
