package org.checkerframework.checker.mungo.assertions

class SymbolicFraction {

}

class SymbolicType {

}

class SymbolicAssertion {

  val id = uuid++

  companion object {
    private var uuid = 1L
  }
}

class NodeAssertions(
  val preThen: SymbolicAssertion,
  val preElse: SymbolicAssertion,
  val postThen: SymbolicAssertion,
  val postElse: SymbolicAssertion
) {

}
