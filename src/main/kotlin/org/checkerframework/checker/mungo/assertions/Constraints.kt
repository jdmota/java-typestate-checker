package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.BoolExpr
import org.checkerframework.checker.mungo.analysis.Reference
import org.checkerframework.checker.mungo.typecheck.*

sealed class Constraint {
  abstract fun toZ3(setup: ConstraintsSetup): BoolExpr
}

class AssertionImpliesAssertion(
  val a: SymbolicAssertion,
  val b: SymbolicAssertion,
  val except: Set<Reference>
) : Constraint() {

  init {
    a.implies(b)
  }

  private fun implies(setup: ConstraintsSetup): BoolExpr {
    val exprs = mutableListOf<BoolExpr>()
    a.forEach { ref, info ->
      if (!except.contains(ref)) {
        exprs.add(SymFractionImpliesSymFraction(info.fraction, b.getAccess(ref)).toZ3(setup))
        exprs.add(SymTypeImpliesSymType(info.type, b.getType(ref)).toZ3(setup))
      }
    }
    return setup.ctx.mkAnd(*exprs.toTypedArray())
  }

  private fun eq(setup: ConstraintsSetup): BoolExpr {
    val exprs = mutableListOf<BoolExpr>()
    a.forEach { ref, info ->
      if (!except.contains(ref)) {
        exprs.add(SymFractionEqSymFraction(info.fraction, b.getAccess(ref)).toZ3(setup))
        exprs.add(SymTypeEqSymType(info.type, b.getType(ref)).toZ3(setup))
      }
    }
    return setup.ctx.mkAnd(*exprs.toTypedArray())
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return if (b.impliedByCount() == 1) eq(setup) else implies(setup)
  }
}

// access(x, a) ==> access(x, b)
// a >= b
class SymFractionImpliesSymFraction(val a: SymbolicFraction, val b: SymbolicFraction) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.fractionToExpr(a)
    val expr2 = setup.fractionToExpr(b)
    // setup.addMinimizeObjective(setup.ctx.mkSub(expr1, expr2))
    setup.addMaximizeObjective(expr2)
    return setup.ctx.mkGe(expr1, expr2)
  }
}

class SymFractionEqSymFraction(val a: SymbolicFraction, val b: SymbolicFraction) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkEq(setup.fractionToExpr(a), setup.fractionToExpr(b))
  }
}

// typeof(x, a) ==> typeof(x, b)
// a <: b
// t1 <: t2
class SymTypeImpliesSymType(val a: SymbolicType, val b: SymbolicType) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return setup.mkSubtype(expr1, expr2)
  }
}

class SymTypeEqSymType(val a: SymbolicType, val b: SymbolicType) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return setup.ctx.mkEq(expr1, expr2)
  }
}

class TypeImpliesSymType(val a: MungoType, val b: SymbolicType) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return setup.mkSubtype(expr1, expr2)
  }
}

class SymTypeImpliesType(val a: SymbolicType, val b: MungoType) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return setup.mkSubtype(expr1, expr2)
  }
}

class SymFractionGt(val a: SymbolicFraction, val b: Int) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkGt(setup.fractionToExpr(a), setup.ctx.mkReal(b))
  }
}

class SymFractionEq(val a: SymbolicFraction, val b: Int) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkEq(setup.fractionToExpr(a), setup.ctx.mkReal(b))
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

  /*
  TODO
  void main() {
    Cell c1 = new Cell();
    Cell c2 = c1;
    // access(c1.item, f1) && access(c2.item, f2) && eq(c1,c2)
    // f1 + f2 = 1

    // access(c1.item, f3) && access(c2.item, f4) && eq(c1,c2)
    // f3 = 1
    c1.setItem(new Item());
    // access(c1.item, f5) && access(c2.item, f6) && eq(c1,c2)
    // f3 + f4 == f5 + f6

    // access(c2.item, f7) && access(c1.item, f8) && eq(c1,c2)
    // f7 = 1
    c2.setItem(new Item());
  }
  */

  private val constraints = mutableListOf<Constraint>()

  fun implies(
    a: SymbolicAssertion,
    b: SymbolicAssertion,
    except: Set<Reference> = emptySet()
  ) {
    // a ==> b
    constraints.add(AssertionImpliesAssertion(a, b, except))
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

}
