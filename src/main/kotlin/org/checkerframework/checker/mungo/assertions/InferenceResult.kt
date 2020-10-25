package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Expr
import com.microsoft.z3.Model
import org.checkerframework.checker.mungo.analysis.*

sealed class InferenceResult {

}

class NoSolution(val unsatCore: Array<BoolExpr>) : InferenceResult()

class UnknownSolution(val reason: String?) : InferenceResult()

class Solution(private val setup: ConstraintsSetup, private val model: Model) : InferenceResult() {

  fun get(x: SymbolicFraction): String = model.eval(setup.fractionToExpr(x), true).toString()

  fun get(x: SymbolicType): String = setup.labelToType(model.eval(setup.typeToExpr(x), true).toString()).toString()

  fun equals(assertion: SymbolicAssertion, a: Reference, b: Reference): Expr {
    return model.eval(setup.mkEquals(assertion, a, b), false)
  }

  fun skipRef(ref: Reference): Boolean {
    return when(ref) {
      is FieldAccess -> false
      is ThisReference -> false
      is ClassName -> true
      is LocalVariable -> false
      is ParameterVariable -> false
      is ReturnSpecialVar -> false
      is OldSpecialVar -> false
      is NodeRef -> true
      is UnknownRef -> true
    }
  }

}
