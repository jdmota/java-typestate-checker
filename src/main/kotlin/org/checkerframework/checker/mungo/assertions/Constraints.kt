package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.ArithExpr
import com.microsoft.z3.BoolExpr
import org.checkerframework.checker.mungo.analysis.Reference
import org.checkerframework.checker.mungo.typecheck.*

private sealed class Constraint {
  abstract fun toZ3(setup: ConstraintsSetup): BoolExpr
}

private class ImpliedAssertion(
  val tail: SymbolicAssertion
) : Constraint() {

  // TODO ensure that certain facts are only asserted with enough permission (i.e. isValid)

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val exprs = mutableListOf<BoolExpr>()
    val impliedBy = tail.impliedBy()

    tail.forEach { ref, info ->
      exprs.add(setup.ctx.mkEq(
        setup.fractionToExpr(info.fraction),
        setup.min(impliedBy.map { it.getAccess(ref) })
      ))

      exprs.add(setup.fractionsAccumulation(ref, impliedBy, tail))

      for (head in impliedBy) {
        // exprs.add(SymFractionImpliesSymFraction(head.getAccess(ref), info.fraction).toZ3(setup))
        // exprs.add(SymFractionImpliesSymFraction(head.getAccessDotZero(ref), info.packFraction).toZ3(setup))
        // TODO this is slow...
        exprs.add(SymTypeImpliesSymType(head.getType(ref), info.type).toZ3(setup))
      }
    }

    for ((a, b) in tail.skeleton.equalities) {
      // Equality is true in assertion "tail" if present in the other assertions
      // and with read access to the variables
      exprs.add(
        setup.ctx.mkEq(
          setup.mkEquals(tail, a, b),
          setup.ctx.mkAnd(
            *impliedBy.map {
              setup.mkEquals(it, a, b)
            }.toTypedArray()
          )
        )
      )
    }

    return setup.ctx.mkAnd(*exprs.toTypedArray())
  }
}

private class OnlyEffects(
  val pre: SymbolicAssertion,
  val post: SymbolicAssertion,
  val except: Set<Reference>
) : Constraint() {

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val exprs = mutableListOf<BoolExpr>()
    pre.forEach { ref, info ->
      if (!except.contains(ref)) {
        exprs.add(SymFractionEqSymFraction(info.fraction, post.getAccess(ref)).toZ3(setup))
        exprs.add(SymFractionEqSymFraction(info.packFraction, post.getAccessDotZero(ref)).toZ3(setup))
        exprs.add(SymTypeEqSymType(info.type, post.getType(ref)).toZ3(setup))
        // TODO
      }
    }
    return setup.ctx.mkAnd(*exprs.toTypedArray())
  }
}

// access(x, a) ==> access(x, b)
// a >= b
private class SymFractionImpliesSymFraction(val a: SymbolicFraction, val b: SymbolicFraction) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.fractionToExpr(a)
    val expr2 = setup.fractionToExpr(b)
    return setup.ctx.mkGe(expr1, expr2)
  }
}

private class SymFractionEqSymFraction(val a: SymbolicFraction, val b: SymbolicFraction) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkEq(setup.fractionToExpr(a), setup.fractionToExpr(b))
  }
}

// typeof(x, a) ==> typeof(x, b)
// a <: b
// t1 <: t2
private class SymTypeImpliesSymType(val a: SymbolicType, val b: SymbolicType) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return setup.mkSubtype(expr1, expr2)
  }
}

private class SymTypeEqSymType(val a: SymbolicType, val b: SymbolicType) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return setup.ctx.mkEq(expr1, expr2)
  }
}

private class TypeImpliesSymType(val a: MungoType, val b: SymbolicType) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return setup.mkSubtype(expr1, expr2)
  }
}

private class SymTypeImpliesType(val a: SymbolicType, val b: MungoType) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return setup.mkSubtype(expr1, expr2)
  }
}

private class SymFractionGt(val a: SymbolicFraction, val b: Int) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkGt(setup.fractionToExpr(a), setup.ctx.mkReal(b))
  }
}

private class SymFractionEq(val a: SymbolicFraction, val b: Int) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkEq(setup.fractionToExpr(a), setup.ctx.mkReal(b))
  }
}

private class EqualityInAssertion(val assertion: SymbolicAssertion, val a: Reference, val b: Reference, val bool: Boolean) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr = setup.mkEquals(assertion, a, b)
    return if (bool) expr else setup.ctx.mkNot(expr)
  }
}

class Constraints {

  private lateinit var setup: ConstraintsSetup

  private val types = mutableSetOf(
    MungoUnknownType.SINGLETON,
    MungoObjectType.SINGLETON,
    MungoNoProtocolType.SINGLETON,
    MungoEndedType.SINGLETON,
    MungoNullType.SINGLETON,
    MungoPrimitiveType.SINGLETON,
    MungoMovedType.SINGLETON,
    MungoBottomType.SINGLETON
  )

  fun addType(type: MungoType) {
    types.add(type)
  }

  fun start(): Constraints {
    setup = ConstraintsSetup(types).start()
    return this
  }

  fun end(): Solution? {
    for (constraint in constraints) {
      setup.addAssert(constraint.toZ3(setup))
    }

    println("Solving...")
    return setup.end()
  }

  // Inferred constraints
  private val constraints = mutableListOf<Constraint>()

  // Track assertions that are implied by others
  private val impliedAssertions = mutableSetOf<SymbolicAssertion>()

  fun implies(a: SymbolicAssertion, b: SymbolicAssertion) {
    // a ==> b
    a.implies(b)
    if (impliedAssertions.add(b)) {
      constraints.add(ImpliedAssertion(b))
    }
  }

  fun onlyEffects(
    pre: SymbolicAssertion,
    post: SymbolicAssertion,
    except: Set<Reference>
  ) {
    constraints.add(OnlyEffects(pre, post, except))
  }

  fun one(a: SymbolicFraction) {
    // a == 1
    constraints.add(SymFractionEq(a, 1))
  }

  fun notZero(a: SymbolicFraction) {
    // a > 0
    constraints.add(SymFractionGt(a, 0))
  }

  fun subtype(t1: SymbolicType, t2: MungoType) {
    // t1 <: t2
    addType(t2)
    constraints.add(SymTypeImpliesType(t1, t2))
  }

  fun subtype(t1: MungoType, t2: SymbolicType) {
    // t1 <: t2
    addType(t1)
    constraints.add(TypeImpliesSymType(t1, t2))
  }

  fun equality(assertion: SymbolicAssertion, a: Reference, b: Reference) {
    // eq(a, b)
    constraints.add(EqualityInAssertion(assertion, a, b, true))
  }

  fun notEquality(assertion: SymbolicAssertion, a: Reference, b: Reference) {
    // !eq(a, b)
    constraints.add(EqualityInAssertion(assertion, a, b, false))
  }

}
