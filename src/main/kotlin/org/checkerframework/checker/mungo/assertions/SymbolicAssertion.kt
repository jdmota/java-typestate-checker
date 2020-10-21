package org.checkerframework.checker.mungo.assertions

import org.checkerframework.checker.mungo.analysis.*
import java.lang.StringBuilder

class SymbolicFraction {

  val id = uuid++

  companion object {
    private var uuid = 1L
  }

  fun z3Symbol() = "f$id"

  override fun toString() = z3Symbol()
}

class SymbolicType {

  val id = uuid++

  companion object {
    private var uuid = 1L
  }

  fun z3Symbol() = "t$id"

  override fun toString() = z3Symbol()
}

class SymbolicEquality {

  val id = uuid++

  companion object {
    private var uuid = 1L
  }

  fun z3Symbol() = "eq$id"

  override fun toString() = z3Symbol()
}

class SymbolicPacked {}

class SymbolicInfo {
  val fraction = SymbolicFraction() // access(x, f1)
  val type = SymbolicType() // typeof(x, t1)
  val packed = SymbolicPacked() // packed(x) or unpacked(x)
  val packFraction = SymbolicFraction() // access(x.0, f2)
  val children = mutableMapOf<Reference, SymbolicInfo>()

  fun forEach(fn: (Reference, SymbolicInfo) -> Unit) {
    for ((ref, info) in children) {
      fn(ref, info)
      info.forEach(fn)
    }
  }

  fun toString(str: StringBuilder, ref: Reference, solution: Solution) {
    str.appendLine("acc($ref,${solution.get(fraction)}) && acc($ref.0,${solution.get(packFraction)}) && typeof($ref,${solution.get(type)})")
    for ((child, info) in children) {
      info.toString(str, child, solution)
    }
  }
}

class SymbolicAssertionSkeleton(
  val locations: Set<Reference>,
  val equalities: Set<Pair<Reference, Reference>>
) {
  companion object {
    val empty = SymbolicAssertionSkeleton(emptySet(), emptySet())
  }

  private val eqTracker = MutableEqualityTracker()

  init {
    for ((a, b) in equalities) {
      eqTracker.setEquality(a, b)
    }
  }

  fun getPossibleEq(ref: Reference) = eqTracker[ref]

  fun create() = SymbolicAssertion(this)
}

class SymbolicAssertion(val skeleton: SymbolicAssertionSkeleton) {

  val id = uuid++

  companion object {
    private var uuid = 1L
  }

  private val impliedBy = mutableSetOf<SymbolicAssertion>()
  private val implies = mutableSetOf<SymbolicAssertion>()

  fun implies(other: SymbolicAssertion) {
    if (this !== other) {
      // this ==> other
      implies.add(other)
      other.impliedBy.add(this)
    }
  }

  fun impliedByCount() = impliedBy.size

  val roots = mutableMapOf<Reference, SymbolicInfo>()

  init {
    for (loc in skeleton.locations) {
      prepare(loc)
    }
  }

  fun prepare(ref: Reference): SymbolicInfo {
    return when (ref) {
      is LocalVariable,
      is ThisReference,
      is ClassName,
      is ReturnSpecialVar,
      is OldSpecialVar -> {
        roots.computeIfAbsent(ref) { SymbolicInfo() }
      }
      is FieldAccess -> {
        val parent = prepare(ref.receiver)
        parent.children.computeIfAbsent(ref) { SymbolicInfo() }
      }
    }
  }

  fun get(ref: Reference): SymbolicInfo {
    return when (ref) {
      is LocalVariable,
      is ThisReference,
      is ClassName,
      is ReturnSpecialVar,
      is OldSpecialVar -> {
        roots[ref] ?: error("No info for $ref")
      }
      is FieldAccess -> {
        val parent = get(ref.receiver)
        parent.children[ref] ?: error("No info for $ref")
      }
    }
  }

  fun getAccess(ref: Reference) = get(ref).fraction

  fun getAccessDotZero(ref: Reference) = get(ref).packFraction

  fun getType(ref: Reference) = get(ref).type

  fun forEach(fn: (Reference, SymbolicInfo) -> Unit) {
    for ((ref, info) in roots) {
      fn(ref, info)
      info.forEach(fn)
    }
  }

  fun toString(solution: Solution): String {
    val str = StringBuilder()
    for ((ref, info) in roots) {
      info.toString(str, ref, solution)
    }
    return str.toString()
  }

  override fun toString(): String {
    return "SymbolicAssertion"
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
      print("then: $preThenStr;\nelse: $preElseStr")
    } else {
      print(preThenStr)
    }
    println("\n$middle\n")
    val postThenStr = postThen.toString(solution)
    val postElseStr = postElse.toString(solution)
    if (postThenStr != postElseStr) {
      print("then: $postThenStr;\nelse: $postElseStr")
    } else {
      print(postThenStr)
    }
    println("----")
  }

}
