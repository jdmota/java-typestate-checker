package org.checkerframework.checker.mungo.assertions

class Constraints {

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
