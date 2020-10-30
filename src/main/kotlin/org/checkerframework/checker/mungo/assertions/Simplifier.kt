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

class GatherSymbols(val symbols: MutableSet<TinyExpr<*, *>> = mutableSetOf()) : Substitution {
  override fun get(expr: TinyExpr<*, *>): TinyExpr<*, *>? {
    when (expr) {
      is TinySomeFraction -> symbols.add(expr)
      is TinySomeType -> symbols.add(expr)
      else -> {
      }
    }
    return expr
  }
}

class Simplifier(experimental: Boolean = false) : Substitution {

  private val allEqualities = GenericEqualityTracker<TinyExpr<*, *>> { it is TinyReal || it is TinyMungoType || it is TinyBool }

  private val shouldTrack = if (experimental) { it: TinyExpr<*, *> ->
    it is TinySomeFraction || it is TinySomeType || it is TinyReal || it is TinyMungoType || it is TinyEquals || it is TinyBoolExpr
  } else { it: TinyExpr<*, *> ->
    it is TinySomeFraction || it is TinySomeType
  }

  override operator fun get(expr: TinyExpr<*, *>): TinyExpr<*, *>? {
    return allEqualities[expr]
  }

  fun track(expr: TinyBoolExpr): TinyBoolExpr? {
    if (expr === Make.TRUE) {
      return null
    }
    return when (expr) {
      is TinyEqArith -> if (shouldTrack(expr.a) && shouldTrack(expr.b)) {
        allEqualities[expr.a] = expr.b
        null
      } else expr
      is TinyEqMungoType -> if (shouldTrack(expr.a) && shouldTrack(expr.b)) {
        allEqualities[expr.a] = expr.b
        null
      } else expr
      is TinyEqBool -> if (shouldTrack(expr.a) && shouldTrack(expr.b)) {
        allEqualities[expr.a] = expr.b
        null
      } else expr
      is TinyEquals -> if (shouldTrack(expr)) {
        allEqualities[expr] = Make.TRUE
        null
      } else expr
      is TinyNot -> if (shouldTrack(expr.bool)) {
        allEqualities[expr.bool] = Make.FALSE
        null
      } else expr
      else -> if (shouldTrack(expr)) {
        allEqualities[expr] = Make.TRUE
        expr
      } else expr
    }
  }

  fun simplify(expr: TinyBoolExpr) = expr.substitute(this)

  fun simplifyAll(exprs: Collection<TinyBoolExpr>): Collection<TinyBoolExpr> {
    val falseExprs = mutableSetOf<TinyBoolExpr>()
    var prev = exprs
    var next = exprs
    do {
      prev = next
      next = prev.mapNotNull { track(it) }.map {
        val s = it.substitute(this)
        if (it != Make.FALSE && s == Make.FALSE) falseExprs.add(it)
        s
      }
      if (prev.size == next.size) {
        break
      }
    } while (true)

    val result = mutableSetOf<TinyBoolExpr>()
    result.addAll(next)
    result.remove(Make.FALSE)

    for (expr in falseExprs) {
      val gatherer = GatherSymbols()
      expr.substitute(gatherer)
      for (sym in gatherer.symbols) {
        when (sym) {
          is TinyArithExpr -> result.add(Make.S.eq(sym, allEqualities[sym] as TinyArithExpr))
          is TinyMungoTypeExpr -> result.add(Make.S.eq(sym, allEqualities[sym] as TinyMungoTypeExpr))
          else -> {
          }
        }
      }
      result.add(expr)
    }

    return result
  }

}
