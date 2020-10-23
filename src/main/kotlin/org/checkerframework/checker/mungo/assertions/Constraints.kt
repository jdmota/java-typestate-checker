package org.checkerframework.checker.mungo.assertions

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

      // exprs.add(SymFractionImpliesSymFraction(head.getAccess(ref), info.fraction).toZ3(setup))
      // exprs.add(SymFractionImpliesSymFraction(head.getAccessDotZero(ref), info.packFraction).toZ3(setup))

      // Subtyping constraints are more difficult for Z3 to solve
      // If this assertion is only implied by another one,
      // just add a constraint where the two types are the same
      if (impliedBy.size == 1) {
        exprs.add(SymTypeEqSymType(impliedBy.first().getType(ref), info.type).toZ3(setup))
      } else {
        for (head in impliedBy) {
          exprs.add(SymTypeImpliesSymType(head.getType(ref), info.type).toZ3(setup))
        }
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
      }
    }

    for ((a, b) in post.skeleton.equalities) {
      if (!except.contains(a) && !except.contains(b)) {
        exprs.add(
          setup.ctx.mkEq(
            setup.mkEquals(post, a, b),
            setup.mkEquals(pre, a, b)
          )
        )
      } else if (except.contains(a) && except.contains(b)) {
        // Ignore
        // This situation happens when dealing with assignments, which produce an equality
      } else if (except.contains(a) != except.contains(b)) {
        // One of them (a or b) changed, so invalidate the equality
        exprs.add(
          setup.ctx.mkEq(
            setup.mkEquals(post, a, b),
            setup.ctx.mkFalse()
          )
        )
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

private class SymTypeEqType(val a: SymbolicType, val b: MungoType) : Constraint() {
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

private class NotEqualityInAssertion(
  val assertion: SymbolicAssertion,
  val a: Reference,
  val b: Reference
) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkNot(
      setup.mkEquals(assertion, a, b)
    )
  }
}

private class EqualityInAssertion(
  val assertion: SymbolicAssertion,
  val a: Reference,
  val b: Reference,
  val data: SymbolicInfo
) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val target = assertion[a]
    val expr = assertion[b]
    return setup.ctx.mkAnd(
      setup.mkEquals(assertion, a, b),
      setup.ctx.mkAnd(
        setup.ctx.mkEq(
          setup.ctx.mkAdd(
            setup.fractionToExpr(target.packFraction),
            setup.fractionToExpr(expr.packFraction)
          ),
          setup.fractionToExpr(data.packFraction)
        ),
        // TODO if the fraction is zero, the type should be Unknown instead
        SymTypeEqSymType(target.type, data.type).toZ3(setup),
        SymTypeEqSymType(expr.type, data.type).toZ3(setup)
      )
    )
  }
}

// TODO transfer between fields as well...
private class TransferOfExpressions(
  val target: SymbolicInfo,
  val data: SymbolicInfo
) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkAnd(
      setup.ctx.mkEq(
        setup.fractionToExpr(target.packFraction),
        setup.fractionToExpr(data.packFraction)
      ),
      SymTypeEqSymType(target.type, data.type).toZ3(setup)
    )
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

  fun end(): InferenceResult {
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

  fun same(a: SymbolicFraction, b: SymbolicFraction) {
    // a == b
    constraints.add(SymFractionEqSymFraction(a, b))
  }

  fun nullType(t: SymbolicType) {
    // t == Null
    addType(MungoNullType.SINGLETON)
    constraints.add(SymTypeEqType(t, MungoNullType.SINGLETON))
  }

  fun same(a: SymbolicType, b: SymbolicType) {
    // a == b
    constraints.add(SymTypeEqSymType(a, b))
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

  fun transfer(target: SymbolicInfo, data: SymbolicInfo) {
    constraints.add(TransferOfExpressions(target, data))
  }

  fun equality(assertion: SymbolicAssertion, a: Reference, b: Reference, data: SymbolicInfo) {
    // eq(a, b)
    constraints.add(EqualityInAssertion(assertion, a, b, data))
  }

  fun notEquality(assertion: SymbolicAssertion, a: Reference, b: Reference) {
    // !eq(a, b)
    constraints.add(NotEqualityInAssertion(assertion, a, b))
  }

}
