package org.checkerframework.checker.mungo.assertions

class Constraints {

  private val debug = mutableListOf<String>()

  fun debug() {
    for (str in debug) {
      println(str)
    }
  }

  fun implies(a: SymbolicAssertion, b: SymbolicAssertion) {
    // TODO
    debug.add("${a.id} ==> ${b.id}")
  }

  fun implies(a: SymbolicFraction, b: SymbolicFraction) {
    // access(x, a) ==> access(x, b)
    // a >= b
    // TODO
  }

  fun one(a: SymbolicFraction) {
    // a == 1
    // TODO
  }

  fun bottom(a: SymbolicType) {
    // a <: Bottom
    // TODO
  }

}
