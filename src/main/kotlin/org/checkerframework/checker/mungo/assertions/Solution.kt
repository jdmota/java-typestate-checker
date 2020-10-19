package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.Expr
import com.microsoft.z3.Model

class Solution(private val setup: ConstraintsSetup, private val model: Model) {

  fun get(x: SymbolicFraction): Expr = model.eval(setup.fractionToExpr(x), true)

  fun get(x: SymbolicType): Expr = model.eval(setup.typeToExpr(x), true)

}
