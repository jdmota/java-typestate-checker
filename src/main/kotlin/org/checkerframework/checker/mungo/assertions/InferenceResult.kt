package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.Expr
import com.microsoft.z3.Model
import org.checkerframework.checker.mungo.analysis.Reference

sealed class InferenceResult

class NoSolution : InferenceResult()

class UnknownSolution : InferenceResult()

class Solution(private val setup: ConstraintsSetup, private val model: Model) : InferenceResult() {

  fun get(x: SymbolicFraction): Expr = model.eval(setup.fractionToExpr(x), true)

  fun get(x: SymbolicType): Expr = model.eval(setup.typeToExpr(x), true)

  fun equals(assertion: SymbolicAssertion, a: Reference, b: Reference): Expr {
    return model.eval(setup.mkEquals(assertion, a, b), false)
  }

}
