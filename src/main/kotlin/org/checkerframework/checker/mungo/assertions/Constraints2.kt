package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.ArithExpr
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Expr
import org.checkerframework.checker.mungo.analysis.Reference
import org.checkerframework.checker.mungo.typecheck.MungoBottomType
import org.checkerframework.checker.mungo.typecheck.MungoType
import org.checkerframework.checker.mungo.typecheck.MungoUnknownType

sealed class TinyExpr<E : TinyExpr<E, Z>, Z : Expr> {
  abstract fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): E
  abstract fun toZ3(setup: ConstraintsSetup): Z
}

sealed class TinyBoolExpr : TinyExpr<TinyBoolExpr, BoolExpr>()

sealed class TinyArithExpr : TinyExpr<TinyArithExpr, ArithExpr>()

sealed class TinyMungoTypeExpr : TinyExpr<TinyMungoTypeExpr, Expr>()

class TinySomeFraction(val key: String) : TinyArithExpr() {
  override fun equals(other: Any?): Boolean {
    return other is TinySomeFraction && key == other.key
  }

  override fun hashCode(): Int {
    return key.hashCode()
  }

  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyArithExpr {
    return map[this] as? TinyArithExpr ?: this
  }

  override fun toZ3(setup: ConstraintsSetup): ArithExpr {
    return setup.mkFraction(key)
  }
}

class TinySomeType(val key: String) : TinyMungoTypeExpr() {
  override fun equals(other: Any?): Boolean {
    return other is TinySomeType && key == other.key
  }

  override fun hashCode(): Int {
    return key.hashCode()
  }

  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyMungoTypeExpr {
    return map[this] as? TinyMungoTypeExpr ?: this
  }

  override fun toZ3(setup: ConstraintsSetup): Expr {
    return setup.mkType(key)
  }
}

class TinyMungoType(val type: MungoType) : TinyMungoTypeExpr() {
  override fun equals(other: Any?): Boolean {
    return other is TinyMungoType && type == other.type
  }

  override fun hashCode(): Int {
    return type.hashCode()
  }

  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyMungoTypeExpr {
    return this
  }

  override fun toZ3(setup: ConstraintsSetup): Expr {
    return setup.mkType(type)
  }
}

class TinyAdd(val list: Collection<TinyArithExpr>) : TinyArithExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyArithExpr {
    return Make.S.add(list.map { it.substitute(map) })
  }

  override fun toZ3(setup: ConstraintsSetup): ArithExpr {
    return setup.ctx.mkAdd(*list.map { it.toZ3(setup) }.toTypedArray())
  }
}

class TinySub(val a: TinyArithExpr, val b: TinyArithExpr) : TinyArithExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyArithExpr {
    return Make.S.sub(a.substitute(map), b.substitute(map))
  }

  override fun toZ3(setup: ConstraintsSetup): ArithExpr {
    return setup.ctx.mkSub(a.toZ3(setup), b.toZ3(setup))
  }
}

class TinyGt(val a: TinyArithExpr, val b: TinyArithExpr) : TinyBoolExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyBoolExpr {
    return Make.S.gt(a.substitute(map), b.substitute(map))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkGt(a.toZ3(setup), b.toZ3(setup))
  }
}

class TinyLt(val a: TinyArithExpr, val b: TinyArithExpr) : TinyBoolExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyBoolExpr {
    return Make.S.lt(a.substitute(map), b.substitute(map))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkLt(a.toZ3(setup), b.toZ3(setup))
  }
}

class TinyGe(val a: TinyArithExpr, val b: TinyArithExpr) : TinyBoolExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyBoolExpr {
    return Make.S.ge(a.substitute(map), b.substitute(map))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkGe(a.toZ3(setup), b.toZ3(setup))
  }
}

class TinyLe(val a: TinyArithExpr, val b: TinyArithExpr) : TinyBoolExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyBoolExpr {
    return Make.S.le(a.substitute(map), b.substitute(map))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkLe(a.toZ3(setup), b.toZ3(setup))
  }
}

class TinyITEArith(
  val condition: TinyBoolExpr,
  val thenExpr: TinyArithExpr,
  val elseExpr: TinyArithExpr
) : TinyArithExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyArithExpr {
    return Make.S.ite(
      condition.substitute(map),
      thenExpr.substitute(map),
      elseExpr.substitute(map)
    )
  }

  override fun toZ3(setup: ConstraintsSetup): ArithExpr {
    return setup.ctx.mkITE(
      condition.toZ3(setup),
      thenExpr.toZ3(setup),
      elseExpr.toZ3(setup)
    ) as ArithExpr
  }
}

class TinyITEBool(
  val condition: TinyBoolExpr,
  val thenExpr: TinyBoolExpr,
  val elseExpr: TinyBoolExpr
) : TinyBoolExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyBoolExpr {
    return Make.S.ite(
      condition.substitute(map),
      thenExpr.substitute(map),
      elseExpr.substitute(map)
    )
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkITE(
      condition.toZ3(setup),
      thenExpr.toZ3(setup),
      elseExpr.toZ3(setup)
    ) as BoolExpr
  }
}

class TinyITEMungoType(
  val condition: TinyBoolExpr,
  val thenExpr: TinyMungoTypeExpr,
  val elseExpr: TinyMungoTypeExpr
) : TinyMungoTypeExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyMungoTypeExpr {
    return Make.S.ite(
      condition.substitute(map),
      thenExpr.substitute(map),
      elseExpr.substitute(map)
    )
  }

  override fun toZ3(setup: ConstraintsSetup): Expr {
    return setup.ctx.mkITE(
      condition.toZ3(setup),
      thenExpr.toZ3(setup),
      elseExpr.toZ3(setup)
    )
  }
}

class TinyReal(val num: Int) : TinyArithExpr() {
  override fun equals(other: Any?): Boolean {
    return other is TinyReal && num == other.num
  }

  override fun hashCode(): Int {
    return num
  }

  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyArithExpr {
    return this
  }

  override fun toZ3(setup: ConstraintsSetup): ArithExpr {
    return setup.ctx.mkReal(num)
  }
}

class TinyNot(val bool: TinyBoolExpr) : TinyBoolExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyBoolExpr {
    return Make.S.not(bool.substitute(map))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkNot(bool.toZ3(setup))
  }
}

class TinyBool(val bool: Boolean) : TinyBoolExpr() {
  override fun equals(other: Any?): Boolean {
    return other is TinyBool && bool == other.bool
  }

  override fun hashCode(): Int {
    return bool.hashCode()
  }

  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyBoolExpr {
    return this
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkBool(bool)
  }
}

class TinyEqArith(val a: TinyArithExpr, val b: TinyArithExpr) : TinyBoolExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyBoolExpr {
    return Make.S.eq(a.substitute(map), b.substitute(map))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkEq(a.toZ3(setup), b.toZ3(setup))
  }
}

class TinyEqBool(val a: TinyBoolExpr, val b: TinyBoolExpr) : TinyBoolExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyBoolExpr {
    return Make.S.eq(a.substitute(map), b.substitute(map))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkEq(a.toZ3(setup), b.toZ3(setup))
  }
}

class TinyEqMungoType(val a: TinyMungoTypeExpr, val b: TinyMungoTypeExpr) : TinyBoolExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyBoolExpr {
    return Make.S.eq(a.substitute(map), b.substitute(map))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkEq(a.toZ3(setup), b.toZ3(setup))
  }
}

class TinyAnd(val list: Collection<TinyBoolExpr>) : TinyBoolExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyBoolExpr {
    return Make.S.and(list.map { it.substitute(map) })
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkAnd(*list.map { it.toZ3(setup) }.toTypedArray())
  }
}

class TinyOr(val list: Collection<TinyBoolExpr>) : TinyBoolExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyBoolExpr {
    return Make.S.or(list.map { it.substitute(map) })
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkOr(*list.map { it.toZ3(setup) }.toTypedArray())
  }
}

class TinyMin(val list: Collection<TinyArithExpr>) : TinyArithExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyArithExpr {
    return Make.S.min(list.map { it.substitute(map) })
  }

  override fun toZ3(setup: ConstraintsSetup): ArithExpr {
    val iterator = list.iterator()
    var expr = iterator.next().toZ3(setup)
    while (iterator.hasNext()) {
      expr = setup.mkMin(expr, iterator.next().toZ3(setup))
    }
    return expr
  }
}

class TinyEquals(val assertion: SymbolicAssertion, val a: Reference, val b: Reference) : TinyBoolExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyBoolExpr {
    return Make.S.equals(assertion, a, b)
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.mkEquals(assertion, a, b)
  }
}

class TinySubtype(val a: TinyMungoTypeExpr, val b: TinyMungoTypeExpr) : TinyBoolExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyBoolExpr {
    return Make.S.subtype(a.substitute(map), b.substitute(map))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.mkSubtype(a.toZ3(setup), b.toZ3(setup))
  }
}

class TinyIntersection(val list: Collection<TinyMungoTypeExpr>) : TinyMungoTypeExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyMungoTypeExpr {
    return Make.S.intersection(list.map { it.substitute(map) })
  }

  override fun toZ3(setup: ConstraintsSetup): Expr {
    val iterator = list.iterator()
    var expr = iterator.next().toZ3(setup)
    while (iterator.hasNext()) {
      expr = setup.mkIntersection(expr, iterator.next().toZ3(setup))
    }
    return expr
  }
}

class TinyUnion(val list: Collection<TinyMungoTypeExpr>) : TinyMungoTypeExpr() {
  override fun substitute(map: Map<TinyExpr<*, *>, TinyExpr<*, *>>): TinyMungoTypeExpr {
    return Make.S.union(list.map { it.substitute(map) })
  }

  override fun toZ3(setup: ConstraintsSetup): Expr {
    val iterator = list.iterator()
    var expr = iterator.next().toZ3(setup)
    while (iterator.hasNext()) {
      expr = setup.mkUnion(expr, iterator.next().toZ3(setup))
    }
    return expr
  }
}

class Make private constructor() {

  fun add(list: Collection<TinyArithExpr>): TinyArithExpr {
    val l = list.filterNot { it == ZERO }
    return when {
      l.isEmpty() -> ZERO
      l.size == 1 -> l.first()
      else -> TinyAdd(l)
    }
  }

  fun sub(a: TinyArithExpr, b: TinyArithExpr): TinyArithExpr {
    return if (b == ZERO) {
      a
    } else if (a is TinyReal && b is TinyReal) {
      TinyReal(a.num - b.num)
    } else {
      TinySub(a, b)
    }
  }

  fun gt(a: TinyArithExpr, b: TinyArithExpr): TinyBoolExpr {
    return if (a is TinyReal && b is TinyReal) {
      bool(a.num > b.num)
    } else {
      TinyGt(a, b)
    }
  }

  fun lt(a: TinyArithExpr, b: TinyArithExpr): TinyBoolExpr {
    return if (a is TinyReal && b is TinyReal) {
      bool(a.num < b.num)
    } else {
      TinyLt(a, b)
    }
  }

  fun ge(a: TinyArithExpr, b: TinyArithExpr): TinyBoolExpr {
    return if (a is TinyReal && b is TinyReal) {
      bool(a.num >= b.num)
    } else {
      TinyGe(a, b)
    }
  }

  fun le(a: TinyArithExpr, b: TinyArithExpr): TinyBoolExpr {
    return if (a is TinyReal && b is TinyReal) {
      bool(a.num <= b.num)
    } else {
      TinyLe(a, b)
    }
  }

  fun ite(condition: TinyBoolExpr, a: TinyArithExpr, b: TinyArithExpr): TinyArithExpr {
    return when {
      condition == TRUE -> a
      condition == FALSE -> b
      a == b -> a
      else -> TinyITEArith(condition, a, b)
    }
  }

  fun ite(condition: TinyBoolExpr, a: TinyBoolExpr, b: TinyBoolExpr): TinyBoolExpr {
    return when {
      condition == TRUE -> a
      condition == FALSE -> b
      a == b -> a
      else -> TinyITEBool(condition, a, b)
    }
  }

  fun ite(condition: TinyBoolExpr, a: TinyMungoTypeExpr, b: TinyMungoTypeExpr): TinyMungoTypeExpr {
    return when {
      condition == TRUE -> a
      condition == FALSE -> b
      a == b -> a
      else -> TinyITEMungoType(condition, a, b)
    }
  }

  fun real(num: Int) = when (num) {
    0 -> ZERO
    1 -> ONE
    else -> TinyReal(num)
  }

  fun not(bool: TinyBoolExpr): TinyBoolExpr {
    return when (bool) {
      TRUE -> FALSE
      FALSE -> TRUE
      else -> TinyNot(bool)
    }
  }

  fun bool(bool: Boolean) = if (bool) TRUE else FALSE

  fun eq(a: TinyArithExpr, b: TinyArithExpr): TinyBoolExpr {
    return if (a == b) TRUE else TinyEqArith(a, b)
  }

  fun eq(a: TinyBoolExpr, b: TinyBoolExpr): TinyBoolExpr {
    return when {
      a == TRUE -> b
      b == TRUE -> a
      a == FALSE -> not(b)
      b == FALSE -> not(a)
      else -> TinyEqBool(a, b)
    }
  }

  fun eq(a: TinyMungoTypeExpr, b: TinyMungoTypeExpr): TinyBoolExpr {
    return if (a == b) TRUE else TinyEqMungoType(a, b)
  }

  fun and(list: Collection<TinyBoolExpr>): TinyBoolExpr {
    val set = list.toSet()
    if (set.contains(FALSE))
      return FALSE

    val l = set.minus(TRUE)

    return when {
      l.isEmpty() -> TRUE
      l.size == 1 -> l.first()
      else -> TinyAnd(l)
    }
  }

  fun or(list: Collection<TinyBoolExpr>): TinyBoolExpr {
    val set = list.toSet()
    if (set.contains(TRUE))
      return TRUE

    val l = set.minus(FALSE)

    return when {
      l.isEmpty() -> FALSE
      l.size == 1 -> l.first()
      else -> TinyOr(l)
    }
  }

  // Compute the minimum between all these values
  // Assuming that they are all between 0 and 1
  fun min(list: Collection<TinyArithExpr>): TinyArithExpr {
    val set = list.toSet()
    if (set.contains(ZERO))
      return ZERO

    val l = set.minus(ONE)

    return when {
      l.isEmpty() -> ONE
      l.size == 1 -> l.first()
      else -> TinyMin(l)
    }
  }

  fun equals(assertion: SymbolicAssertion, a: Reference, b: Reference): TinyBoolExpr {
    return when {
      a == b -> TRUE
      assertion.skeleton.equalities.contains(Pair(a, b)) -> TinyEquals(assertion, a, b)
      assertion.skeleton.equalities.contains(Pair(b, a)) -> TinyEquals(assertion, b, a)
      else -> FALSE
    }
  }

  fun subtype(a: TinyMungoTypeExpr, b: TinyMungoTypeExpr): TinyBoolExpr {
    return if (a is TinyMungoType && b is TinyMungoType) {
      bool(a.type.isSubtype(b.type))
    } else {
      TinySubtype(a, b)
    }
  }

  fun intersection(list: Collection<TinyMungoTypeExpr>): TinyMungoTypeExpr {
    val set = list.toSet()
    if (set.contains(BOTTOM))
      return BOTTOM

    val l = set.minus(UNKNOWN)

    return when {
      l.isEmpty() -> UNKNOWN
      l.size == 1 -> l.first()
      else -> TinyIntersection(l)
    }
  }

  fun union(list: Collection<TinyMungoTypeExpr>): TinyMungoTypeExpr {
    val set = list.toSet()
    if (set.contains(UNKNOWN))
      return UNKNOWN

    val l = set.minus(BOTTOM)

    return when {
      l.isEmpty() -> BOTTOM
      l.size == 1 -> l.first()
      else -> TinyUnion(l)
    }
  }

  // exists x :: eq(a, x) && eq(x, b)
  fun equalsTransitive(assertion: SymbolicAssertion, a: Reference, b: Reference): TinyBoolExpr {
    // "a" and "b" are in this set
    val possibleEqualities = assertion.skeleton.getPossibleEq(a)
    val others = possibleEqualities.filterNot { it == a || it == b }
    return or(others.map {
      and(listOf(
        equals(assertion, a, it),
        equals(assertion, it, b)
      ))
    })
  }

  fun fraction(key: String) = TinySomeFraction(key)

  fun type(key: String) = TinySomeType(key)

  fun type(type: MungoType) = TinyMungoType(type)

  companion object {
    val S = Make()
    val ZERO = TinyReal(0)
    val ONE = TinyReal(1)
    val TRUE = TinyBool(true)
    val FALSE = TinyBool(false)
    val UNKNOWN = TinyMungoType(MungoUnknownType.SINGLETON)
    val BOTTOM = TinyMungoType(MungoBottomType.SINGLETON)
  }
}
