package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.Model
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

  private val impliedBy = mutableSetOf<SymbolicAssertion>()

  fun impliedBy(other: SymbolicAssertion) {
    if (this !== other) impliedBy.add(other)
  }

  fun getImpliedBy(): Set<SymbolicAssertion> = impliedBy

  private val accesses = mutableMapOf<Reference, SymbolicFraction>()
  private val typeofs = mutableMapOf<Reference, SymbolicType>()

  init {
    for (loc in locations) {
      accesses[loc] = SymbolicFraction()
      typeofs[loc] = SymbolicType()
    }
  }

  fun getAccesses(): Map<Reference, SymbolicFraction> = accesses

  fun getTypeofs(): Map<Reference, SymbolicType> = typeofs

  fun getAccess(ref: Reference) = accesses[ref] ?: error("No fraction for $ref")

  fun getType(ref: Reference) = typeofs[ref] ?: error("No type for $ref")

  fun toString(solution: Solution): String {
    val str = StringBuilder()
    for ((loc, f) in accesses) {
      str.append("acc($loc,${solution.get(f)}) && ")
    }
    str.append('\n')
    for ((loc, t) in typeofs) {
      str.append("typeof($loc,${solution.get(t)}) && ")
    }
    return str.toString()
  }

  override fun toString(): String {
    val str = StringBuilder()
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
    println("----")
    val preThenStr = preThen.toString()
    val preElseStr = preElse.toString()
    if (preThenStr != preElseStr) {
      println("then: $preThenStr;\nelse: $preElseStr")
    } else {
      println(preThenStr)
    }
    println("\n$middle\n")
    val postThenStr = postThen.toString()
    val postElseStr = postElse.toString()
    if (postThenStr != postElseStr) {
      println("then: $postThenStr;\nelse: $postElseStr")
    } else {
      println(postThenStr)
    }
    println("----")
  }

  fun debug(solution: Solution, middle: String) {
    println("----")
    val preThenStr = preThen.toString(solution)
    val preElseStr = preElse.toString(solution)
    if (preThenStr != preElseStr) {
      println("then: $preThenStr;\nelse: $preElseStr")
    } else {
      println(preThenStr)
    }
    println("\n$middle\n")
    val postThenStr = postThen.toString(solution)
    val postElseStr = postElse.toString(solution)
    if (postThenStr != postElseStr) {
      println("then: $postThenStr;\nelse: $postElseStr")
    } else {
      println(postThenStr)
    }
    println("----")
  }

}
