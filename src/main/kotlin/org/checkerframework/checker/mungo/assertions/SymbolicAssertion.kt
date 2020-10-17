package org.checkerframework.checker.mungo.assertions

import org.checkerframework.checker.mungo.analysis.Reference

class SymbolicFraction {

}

class SymbolicType {

}

class SymbolicAssertion(val locations: Set<Reference>) {

  val id = uuid++

  companion object {
    private var uuid = 1L
  }

  override fun toString(): String {
    return "($id) $locations"
  }
}

class NodeAssertions(
  val preThen: SymbolicAssertion,
  val preElse: SymbolicAssertion,
  val postThen: SymbolicAssertion,
  val postElse: SymbolicAssertion
) {

}
