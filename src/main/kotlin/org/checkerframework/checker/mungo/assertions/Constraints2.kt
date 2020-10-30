package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.*
import org.checkerframework.checker.mungo.analysis.Reference
import org.checkerframework.checker.mungo.typecheck.MungoBottomType
import org.checkerframework.checker.mungo.typecheck.MungoType
import org.checkerframework.checker.mungo.typecheck.MungoUnknownType

sealed class TinyExpr<E : TinyExpr<E, Z>, Z : Expr> {
  abstract fun substitute(s: Substitution): E
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

  override fun substitute(s: Substitution): TinyArithExpr {
    return s[this] as? TinyArithExpr ?: this
  }

  override fun toZ3(setup: ConstraintsSetup): ArithExpr {
    return setup.mkFraction(key)
  }

  override fun toString(): String {
    return key
  }
}

class TinySomeType(val key: String) : TinyMungoTypeExpr() {
  override fun equals(other: Any?): Boolean {
    return other is TinySomeType && key == other.key
  }

  override fun hashCode(): Int {
    return key.hashCode()
  }

  override fun substitute(s: Substitution): TinyMungoTypeExpr {
    return s[this] as? TinyMungoTypeExpr ?: this
  }

  override fun toZ3(setup: ConstraintsSetup): Expr {
    return setup.mkType(key)
  }

  override fun toString(): String {
    return key
  }
}

class TinyMungoType(val type: MungoType) : TinyMungoTypeExpr() {
  override fun equals(other: Any?): Boolean {
    return other is TinyMungoType && type == other.type
  }

  override fun hashCode(): Int {
    return type.hashCode()
  }

  override fun substitute(s: Substitution): TinyMungoTypeExpr {
    return this
  }

  override fun toZ3(setup: ConstraintsSetup): Expr {
    return setup.mkType(type)
  }

  override fun toString(): String {
    return type.format()
  }
}

class TinyAdd(val list: Collection<TinyArithExpr>) : TinyArithExpr() {
  override fun substitute(s: Substitution): TinyArithExpr {
    return Make.S.add(list.map { it.substitute(s) })
  }

  override fun toZ3(setup: ConstraintsSetup): ArithExpr {
    return setup.ctx.mkAdd(*list.map { it.toZ3(setup) }.toTypedArray())
  }

  override fun toString(): String {
    return "(${list.joinToString(" + ")})"
  }
}

class TinySub(val a: TinyArithExpr, val b: TinyArithExpr) : TinyArithExpr() {
  override fun substitute(s: Substitution): TinyArithExpr {
    return Make.S.sub(a.substitute(s), b.substitute(s))
  }

  override fun toZ3(setup: ConstraintsSetup): ArithExpr {
    return setup.ctx.mkSub(a.toZ3(setup), b.toZ3(setup))
  }

  override fun toString(): String {
    return "($a - $b)"
  }
}

class TinyGt(val a: TinyArithExpr, val b: TinyArithExpr) : TinyBoolExpr() {
  override fun substitute(s: Substitution): TinyBoolExpr {
    return Make.S.gt(a.substitute(s), b.substitute(s))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkGt(a.toZ3(setup), b.toZ3(setup))
  }

  override fun equals(other: Any?): Boolean {
    return other is TinyGt && a == other.a && b == other.b
  }

  override fun hashCode(): Int {
    var result = a.hashCode()
    result = 31 * result + b.hashCode()
    return result
  }

  override fun toString(): String {
    return "($a > $b)"
  }
}

class TinyLt(val a: TinyArithExpr, val b: TinyArithExpr) : TinyBoolExpr() {
  override fun substitute(s: Substitution): TinyBoolExpr {
    return Make.S.lt(a.substitute(s), b.substitute(s))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkLt(a.toZ3(setup), b.toZ3(setup))
  }

  override fun equals(other: Any?): Boolean {
    return other is TinyLt && a == other.a && b == other.b
  }

  override fun hashCode(): Int {
    var result = a.hashCode()
    result = 31 * result + b.hashCode()
    return result
  }

  override fun toString(): String {
    return "($a < $b)"
  }
}

class TinyGe(val a: TinyArithExpr, val b: TinyArithExpr) : TinyBoolExpr() {
  override fun substitute(s: Substitution): TinyBoolExpr {
    return Make.S.ge(a.substitute(s), b.substitute(s))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkGe(a.toZ3(setup), b.toZ3(setup))
  }

  override fun equals(other: Any?): Boolean {
    return other is TinyGe && a == other.a && b == other.b
  }

  override fun hashCode(): Int {
    var result = a.hashCode()
    result = 31 * result + b.hashCode()
    return result
  }

  override fun toString(): String {
    return "($a >= $b)"
  }
}

class TinyLe(val a: TinyArithExpr, val b: TinyArithExpr) : TinyBoolExpr() {
  override fun substitute(s: Substitution): TinyBoolExpr {
    return Make.S.le(a.substitute(s), b.substitute(s))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkLe(a.toZ3(setup), b.toZ3(setup))
  }

  override fun equals(other: Any?): Boolean {
    return other is TinyLe && a == other.a && b == other.b
  }

  override fun hashCode(): Int {
    var result = a.hashCode()
    result = 31 * result + b.hashCode()
    return result
  }

  override fun toString(): String {
    return "($a <= $b)"
  }
}

class TinyITEArith(
  val condition: TinyBoolExpr,
  val thenExpr: TinyArithExpr,
  val elseExpr: TinyArithExpr
) : TinyArithExpr() {
  override fun substitute(s: Substitution): TinyArithExpr {
    return Make.S.ite(
      condition.substitute(s),
      thenExpr.substitute(s),
      elseExpr.substitute(s)
    )
  }

  override fun toZ3(setup: ConstraintsSetup): ArithExpr {
    return setup.ctx.mkITE(
      condition.toZ3(setup),
      thenExpr.toZ3(setup),
      elseExpr.toZ3(setup)
    ) as ArithExpr
  }

  override fun toString(): String {
    return "(if $condition then $thenExpr else $elseExpr)"
  }
}

class TinyITEBool(
  val condition: TinyBoolExpr,
  val thenExpr: TinyBoolExpr,
  val elseExpr: TinyBoolExpr
) : TinyBoolExpr() {
  override fun substitute(s: Substitution): TinyBoolExpr {
    return Make.S.ite(
      condition.substitute(s),
      thenExpr.substitute(s),
      elseExpr.substitute(s)
    )
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkITE(
      condition.toZ3(setup),
      thenExpr.toZ3(setup),
      elseExpr.toZ3(setup)
    ) as BoolExpr
  }

  override fun toString(): String {
    return "(if $condition then $thenExpr else $elseExpr)"
  }
}

class TinyITEMungoType(
  val condition: TinyBoolExpr,
  val thenExpr: TinyMungoTypeExpr,
  val elseExpr: TinyMungoTypeExpr
) : TinyMungoTypeExpr() {
  override fun substitute(s: Substitution): TinyMungoTypeExpr {
    return Make.S.ite(
      condition.substitute(s),
      thenExpr.substitute(s),
      elseExpr.substitute(s)
    )
  }

  override fun toZ3(setup: ConstraintsSetup): Expr {
    return setup.ctx.mkITE(
      condition.toZ3(setup),
      thenExpr.toZ3(setup),
      elseExpr.toZ3(setup)
    )
  }

  override fun toString(): String {
    return "(if $condition then $thenExpr else $elseExpr)"
  }
}

class TinyReal(val num: Int, val denominator: Int = 1) : TinyArithExpr() {
  override fun equals(other: Any?): Boolean {
    return other is TinyReal && num * other.denominator == other.num * denominator
  }

  override fun hashCode(): Int {
    return num
  }

  override fun substitute(s: Substitution): TinyArithExpr {
    return this
  }

  override fun toZ3(setup: ConstraintsSetup): ArithExpr {
    return if (denominator == 1) setup.ctx.mkReal(num) else setup.ctx.mkReal(num, denominator)
  }

  override fun toString(): String {
    return if (denominator == 1) "$num" else "$num/$denominator"
  }
}

class TinyNot(val bool: TinyBoolExpr) : TinyBoolExpr() {
  override fun substitute(s: Substitution): TinyBoolExpr {
    return Make.S.not(bool.substitute(s))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkNot(bool.toZ3(setup))
  }

  override fun toString(): String {
    return "(not $bool)"
  }
}

class TinyBool(val bool: Boolean) : TinyBoolExpr() {
  override fun equals(other: Any?): Boolean {
    return other is TinyBool && bool == other.bool
  }

  override fun hashCode(): Int {
    return bool.hashCode()
  }

  override fun substitute(s: Substitution): TinyBoolExpr {
    return this
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkBool(bool)
  }

  override fun toString(): String {
    return "$bool"
  }
}

class TinyEqArith(val a: TinyArithExpr, val b: TinyArithExpr) : TinyBoolExpr() {
  override fun substitute(s: Substitution): TinyBoolExpr {
    return Make.S.eq(a.substitute(s), b.substitute(s))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkEq(a.toZ3(setup), b.toZ3(setup))
  }

  override fun toString(): String {
    return "($a = $b)"
  }
}

class TinyEqBool(val a: TinyBoolExpr, val b: TinyBoolExpr) : TinyBoolExpr() {
  override fun substitute(s: Substitution): TinyBoolExpr {
    return Make.S.eq(a.substitute(s), b.substitute(s))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkEq(a.toZ3(setup), b.toZ3(setup))
  }

  override fun toString(): String {
    return "($a = $b)"
  }
}

class TinyEqMungoType(val a: TinyMungoTypeExpr, val b: TinyMungoTypeExpr) : TinyBoolExpr() {
  override fun substitute(s: Substitution): TinyBoolExpr {
    return Make.S.eq(a.substitute(s), b.substitute(s))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkEq(a.toZ3(setup), b.toZ3(setup))
  }

  override fun toString(): String {
    return "($a = $b)"
  }
}

class TinyAnd(val list: Collection<TinyBoolExpr>) : TinyBoolExpr() {
  override fun substitute(s: Substitution): TinyBoolExpr {
    return Make.S.and(list.map { it.substitute(s) })
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkAnd(*list.map { it.toZ3(setup) }.toTypedArray())
  }

  override fun toString(): String {
    return "(${list.joinToString(" && ")})"
  }
}

class TinyOr(val list: Collection<TinyBoolExpr>) : TinyBoolExpr() {
  override fun substitute(s: Substitution): TinyBoolExpr {
    return Make.S.or(list.map { it.substitute(s) })
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkOr(*list.map { it.toZ3(setup) }.toTypedArray())
  }

  override fun toString(): String {
    return "(${list.joinToString(" || ")})"
  }
}

class TinyMin(val list: Collection<TinyArithExpr>) : TinyArithExpr() {
  override fun substitute(s: Substitution): TinyArithExpr {
    return Make.S.min(list.map { it.substitute(s) })
  }

  override fun toZ3(setup: ConstraintsSetup): ArithExpr {
    val iterator = list.iterator()
    var expr = iterator.next().toZ3(setup)
    while (iterator.hasNext()) {
      expr = setup.mkMin(expr, iterator.next().toZ3(setup))
    }
    return expr
  }

  override fun toString(): String {
    return "(min ${list.joinToString(" ")})"
  }
}

class TinyEquals(val assertion: SymbolicAssertion, val a: Reference, val b: Reference) : TinyBoolExpr() {
  override fun substitute(s: Substitution): TinyBoolExpr {
    return s[this] as? TinyBoolExpr ?: Make.S.equals(assertion, a, b)
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.mkEquals(assertion, a, b)
  }

  override fun equals(other: Any?): Boolean {
    return other is TinyEquals && assertion == other.assertion && a == other.a && b == other.b
  }

  override fun hashCode(): Int {
    var result = assertion.hashCode()
    result = 31 * result + a.hashCode()
    result = 31 * result + b.hashCode()
    return result
  }

  override fun toString(): String {
    return "(eq_${assertion.id} $a $b)"
  }
}

class TinySubtype(val a: TinyMungoTypeExpr, val b: TinyMungoTypeExpr) : TinyBoolExpr() {
  override fun substitute(s: Substitution): TinyBoolExpr {
    return Make.S.subtype(a.substitute(s), b.substitute(s))
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.mkSubtype(a.toZ3(setup), b.toZ3(setup))
  }

  override fun toString(): String {
    return "(subtype $a $b)"
  }
}

class TinyIntersection(val list: Collection<TinyMungoTypeExpr>) : TinyMungoTypeExpr() {
  override fun substitute(s: Substitution): TinyMungoTypeExpr {
    return Make.S.intersection(list.map { it.substitute(s) })
  }

  override fun toZ3(setup: ConstraintsSetup): Expr {
    val iterator = list.iterator()
    var expr = iterator.next().toZ3(setup)
    while (iterator.hasNext()) {
      expr = setup.mkIntersection(expr, iterator.next().toZ3(setup))
    }
    return expr
  }

  override fun toString(): String {
    return "(intersection ${list.joinToString(" ")})"
  }
}

class TinyUnion(val list: Collection<TinyMungoTypeExpr>) : TinyMungoTypeExpr() {
  override fun substitute(s: Substitution): TinyMungoTypeExpr {
    return Make.S.union(list.map { it.substitute(s) })
  }

  override fun toZ3(setup: ConstraintsSetup): Expr {
    val iterator = list.iterator()
    var expr = iterator.next().toZ3(setup)
    while (iterator.hasNext()) {
      expr = setup.mkUnion(expr, iterator.next().toZ3(setup))
    }
    return expr
  }

  override fun toString(): String {
    return "(union ${list.joinToString(" ")})"
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
      TinyReal(
        a.num * b.denominator - b.num * a.denominator,
        a.denominator * b.denominator
      )
    } else {
      TinySub(a, b)
    }
  }

  fun gt(a: TinyArithExpr, b: TinyArithExpr): TinyBoolExpr {
    return if (a is TinyReal && b is TinyReal) {
      bool(a.num * b.denominator > b.num * a.denominator)
    } else {
      TinyGt(a, b)
    }
  }

  fun lt(a: TinyArithExpr, b: TinyArithExpr): TinyBoolExpr {
    return if (a is TinyReal && b is TinyReal) {
      bool(a.num * b.denominator < b.num * a.denominator)
    } else {
      TinyLt(a, b)
    }
  }

  fun ge(a: TinyArithExpr, b: TinyArithExpr): TinyBoolExpr {
    return if (a is TinyReal && b is TinyReal) {
      bool(a.num * b.denominator >= b.num * a.denominator)
    } else {
      TinyGe(a, b)
    }
  }

  fun le(a: TinyArithExpr, b: TinyArithExpr): TinyBoolExpr {
    return if (a is TinyReal && b is TinyReal) {
      bool(a.num * b.denominator <= b.num * a.denominator)
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

  fun real(num: Int, denominator: Int = 1): TinyReal {
    return when (num) {
      0 -> ZERO
      denominator -> ONE
      else -> TinyReal(num, denominator)
    }
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
    return when {
      a == b -> TRUE
      a == ZERO && b is TinySub -> TinyEqArith(b.a, b.b)
      b == ZERO && a is TinySub -> TinyEqArith(a.a, a.b)
      else -> TinyEqArith(a, b)
    }
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
