package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.IntNum
import com.microsoft.z3.RatNum

interface Substitution {
  operator fun get(expr: TinyExpr<*, *>): TinyExpr<*, *>?
}

class SolutionMap(private val solution: SomeSolution) : Substitution {
  override fun get(expr: TinyExpr<*, *>): TinyExpr<*, *>? {
    return when (expr) {
      is TinyBoolExpr -> {
        when (solution.eval(expr).toString()) {
          "true" -> Make.TRUE
          "false" -> Make.FALSE
          else -> null
        }
      }
      is TinyArithExpr -> {
        when (val z3expr = solution.eval(expr)) {
          is RatNum -> Make.S.real(z3expr.numerator.int, z3expr.denominator.int)
          is IntNum -> Make.S.real(z3expr.int)
          else -> null
        }
      }
      else -> null
    }
  }
}

class Simplifier : Substitution {

  private val allEqualities = GenericEqualityTracker<TinyExpr<*, *>> { it is TinyReal || it is TinyMungoType }
  private val track = { it: TinyExpr<*, *> ->
    // FIXME if we uncomment this, simplification breaks?
    // it is TinyReal || it is TinyMungoType ||
    it is TinySomeFraction || it is TinySomeType
  }

  override operator fun get(expr: TinyExpr<*, *>): TinyExpr<*, *>? {
    return allEqualities[expr]
  }

  fun track(expr: TinyBoolExpr): TinyBoolExpr? {
    if (expr === Make.TRUE) {
      return null
    }
    if (expr is TinyEqArith) {
      if (track(expr.a) && track(expr.b)) {
        allEqualities[expr.a] = expr.b
        return null
      }
    } else if (expr is TinyEqMungoType) {
      if (track(expr.a) && track(expr.b)) {
        allEqualities[expr.a] = expr.b
        return null
      }
    }
    return expr
  }

  fun simplify(expr: TinyBoolExpr) = expr.substitute(this)

  fun simplifyAll(exprs: Collection<TinyBoolExpr>): Collection<TinyBoolExpr> {
    var prev = exprs
    var next = exprs
    do {
      prev = next
      next = prev.mapNotNull { track(it) }
      if (prev.size != next.size) {
        next = next.map { it.substitute(this) }
      } else break
    } while (true)
    return next
  }

}
