package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.BoolExpr
import org.checkerframework.checker.mungo.typecheck.*

sealed class Constraint {
  abstract fun toZ3(setup: ConstraintsSetup): BoolExpr
}

class SymFractionImpliesSymFraction(val a: SymbolicFraction, val b: SymbolicFraction) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkGe(setup.fractionToExpr(a), setup.fractionToExpr(b))
  }
}

class SymTypeImpliesSymType(val a: SymbolicType, val b: SymbolicType) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return setup.mkSubtype(expr1, expr2)
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
    return setup.ctx.mkGt(setup.fractionToExpr(a), setup.ctx.mkReal(0))
  }
}

class SymFractionEq(val a: SymbolicFraction, val b: Int) : Constraint() {
  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkEq(setup.fractionToExpr(a), setup.ctx.mkReal(b))
  }
}

class Constraints {

  private val debug = mutableListOf<String>()

  fun debug() {
    for (str in debug) {
      println(str)
    }
    setup.debug()
  }

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

  fun end() {
    for (constraint in constraints) {
      setup.addAssert(constraint.toZ3(setup))
    }

    println("Solving...")
    setup.end()
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

  fun implies(a: SymbolicAssertion, b: SymbolicAssertion) {
    debug.add("${a.id} ==> ${b.id}")

    // a ==> b
    for ((ref, f) in a.getAccesses()) {
      implies(f, b.getAccess(ref))
    }
    for ((ref, t) in a.getTypeofs()) {
      implies(t, b.getType(ref))
    }
  }

  // Greater than instead of equals is important because a node might have multiple ancestors (e.g. loops)
  fun implies(a: SymbolicFraction, b: SymbolicFraction) {
    // access(x, a) ==> access(x, b)
    // a >= b
    constraints.add(SymFractionImpliesSymFraction(a, b))
  }

  fun implies(a: SymbolicType, b: SymbolicType) {
    // typeof(x, a) ==> typeof(x, b)
    // a <: b
    // t1 <: t2
    constraints.add(SymTypeImpliesSymType(a, b))
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
