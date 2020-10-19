package org.checkerframework.checker.mungo.assertions

import org.checkerframework.checker.mungo.typecheck.*
import java.lang.RuntimeException

class Constraints {

  private val debug = mutableListOf<String>()

  fun debug() {
    for (str in debug) {
      println(str)
    }
    setup.debug()
  }

  private lateinit var setup: ConstraintsSetup

  private val singletonTypes = mutableSetOf<MungoType>(
    MungoNoProtocolType.SINGLETON,
    MungoEndedType.SINGLETON,
    MungoNullType.SINGLETON,
    MungoPrimitiveType.SINGLETON,
    MungoMovedType.SINGLETON
  )

  fun addSingletonType(type: MungoType) {
    singletonTypes.add(type)
  }

  fun start(): Constraints {
    setup = ConstraintsSetup(singletonTypes).start()
    return this
  }

  fun end() = setup.end()

  // TODO symbols that are not constrained, should default to 0 fraction and Unknown type??

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

  fun implies(a: SymbolicAssertion, b: SymbolicAssertion) {
    // TODO
    debug.add("${a.id} ==> ${b.id}")
  }

  // Greater than instead of equals is important because a node might have multiple ancestors (e.g. loops)
  fun implies(a: SymbolicFraction, b: SymbolicFraction) {
    // access(x, a) ==> access(x, b)
    // a >= b
    // TODO
  }

  fun implies(a: SymbolicType, b: SymbolicType) {
    // typeof(x, a) ==> typeof(x, b)
    // a <: b
    // TODO
  }

  fun one(a: SymbolicFraction) {
    // a == 1
    // TODO
  }

  fun notZero(a: SymbolicFraction) {
    // a > 0
    // TODO
  }

  fun subtype(t1: SymbolicType, t2: MungoType) {
    // t1 <: t2
    // TODO
  }

  fun subtype(t1: MungoType, t2: SymbolicType) {
    // t1 <: t2
    // TODO
  }

}
