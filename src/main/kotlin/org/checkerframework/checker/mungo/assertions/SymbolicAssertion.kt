package org.checkerframework.checker.mungo.assertions

import org.checkerframework.checker.mungo.analysis.Reference

class SymbolicFraction {

  val id = uuid++

  companion object {
    private var uuid = 1L
  }

  override fun toString(): String {
    return "f$id"
  }
}

class SymbolicType {

  val id = uuid++

  companion object {
    private var uuid = 1L
  }

  override fun toString(): String {
    return "t$id"
  }
}

class SymbolicAssertion(val locations: Set<Reference>) {

  val id = uuid++

  companion object {
    private var uuid = 1L
  }

  private val accesses = mutableMapOf<Reference, SymbolicFraction>()
  private val typeofs = mutableMapOf<Reference, SymbolicType>()

  fun getAccess(ref: Reference) = accesses.computeIfAbsent(ref) { SymbolicFraction() }

  fun getType(ref: Reference) = typeofs.computeIfAbsent(ref) { SymbolicType() }

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
