package org.checkerframework.checker.mungo.assertions

import org.checkerframework.checker.mungo.analysis.Reference
import java.lang.StringBuilder

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

  init {
    for (loc in locations) {
      accesses[loc] = SymbolicFraction()
      typeofs[loc] = SymbolicType()
    }
  }

  fun getAccess(ref: Reference) = accesses[ref] ?: error("No fraction for $ref")

  fun getType(ref: Reference) = typeofs[ref] ?: error("No type for $ref")

  override fun toString(): String {
    val str = StringBuilder("($id) ")
    for ((loc, f) in accesses) {
      str.append("acc($loc,$f) && ")
    }
    str.append('\n')
    for ((loc, t) in typeofs) {
      str.append("typeof($loc,$t) && ")
    }
    return str.toString()
  }
}

class NodeAssertions(
  val preThen: SymbolicAssertion,
  val preElse: SymbolicAssertion,
  val postThen: SymbolicAssertion,
  val postElse: SymbolicAssertion
) {

  fun debug(middle: String) {
    if (preThen !== preElse) {
      println("then: $preThen; else: $preElse")
    } else {
      println(preThen)
    }
    println(middle)
    if (postThen !== postElse) {
      println("then: $postThen; else: $postElse")
    } else {
      println(postThen)
    }
  }

}
