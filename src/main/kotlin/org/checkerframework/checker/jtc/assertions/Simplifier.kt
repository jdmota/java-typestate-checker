package org.checkerframework.checker.jtc.assertions

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

class Simplifier(experimental: Boolean = false, private val setEqualsToFalse: Boolean = false) : Substitution {

  private val allEqualities = GenericEqualityTracker<TinyExpr<*, *>> { it is TinyReal || it is TinyJTCType || it is TinyBool }

  private val shouldTrack = if (experimental) { it: TinyExpr<*, *> ->
    it is TinySomeFraction || it is TinySomeType || it is TinyReal || it is TinyJTCType || it is TinyEquals || it is TinyBoolExpr
  } else { it: TinyExpr<*, *> ->
    it is TinySomeFraction || it is TinySomeType
  }

  override operator fun get(expr: TinyExpr<*, *>): TinyExpr<*, *> {
    val replacement = allEqualities[expr]
    return if (replacement === expr && setEqualsToFalse && expr is TinyEquals) Make.ZERO else replacement
  }

  fun getSame(expr: TinyExpr<*, *>): Set<TinyExpr<*, *>> {
    return allEqualities.aliases(expr)
  }

  fun getSymbols(expr: TinyExpr<*, *>): Set<TinyExpr<*, *>> {
    val gatherer = GatherSymbols()
    expr.substitute(gatherer)
    return gatherer.symbols
  }

  private fun track(expr: TinyBoolExpr): TinyBoolExpr? {
    if (expr === Make.TRUE) {
      return null
    }
    return when (expr) {
      is TinyGe -> if (expr.a is TinySomeFraction && expr.b == Make.ONE) {
        allEqualities[expr.a] = expr.b
        null
      } else expr
      is TinyLe -> if (expr.a == Make.ONE && expr.b is TinySomeFraction) {
        allEqualities[expr.b] = expr.a
        null
      } else expr
      is TinyEqArith -> if (shouldTrack(expr.a) && shouldTrack(expr.b)) {
        allEqualities[expr.a] = expr.b
        null
      } else expr
      is TinyEqJTCType -> if (shouldTrack(expr.a) && shouldTrack(expr.b)) {
        allEqualities[expr.a] = expr.b
        null
      } else expr
      is TinyEqBool -> if (shouldTrack(expr.a) && shouldTrack(expr.b)) {
        allEqualities[expr.a] = expr.b
        null
      } else expr
      /*is TinyEquals -> if (shouldTrack(expr)) {
        allEqualities[expr] = Make.TRUE
        null
      } else expr*/
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

  fun simplifyAll(exprs: Collection<TinyBoolExpr>): Collection<TinyBoolExpr> {
    val falseExprs = mutableSetOf<TinyBoolExpr>()
    var prev = exprs
    var next = exprs
    do {
      prev = next
      next = prev.mapNotNull { track(it) }.map {
        val s = it.substitute(this)
        s.origin = it
        s.phase = it.phase
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
      for (sym in getSymbols(expr)) {
        when (sym) {
          is TinyArithExpr -> result.add(Make.S.eq(sym, allEqualities[sym] as TinyArithExpr))
          is TinyJTCTypeExpr -> result.add(Make.S.eq(sym, allEqualities[sym] as TinyJTCTypeExpr))
          else -> {
          }
        }
      }
      result.add(expr)
    }

    return result
  }

}
