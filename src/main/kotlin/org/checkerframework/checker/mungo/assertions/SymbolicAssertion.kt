package org.checkerframework.checker.mungo.assertions

import org.checkerframework.checker.mungo.analysis.*
import java.lang.StringBuilder

class SymbolicFraction {

  val id = uuid++

  companion object {
    private var uuid = 1L
  }

  fun z3Symbol() = "f$id"

  override fun equals(other: Any?): Boolean {
    return this === other
  }

  override fun hashCode(): Int {
    return id.hashCode()
  }

  override fun toString() = z3Symbol()
}

class SymbolicType {

  val id = uuid++

  companion object {
    private var uuid = 1L
  }

  fun z3Symbol() = "t$id"

  override fun equals(other: Any?): Boolean {
    return this === other
  }

  override fun hashCode(): Int {
    return id.hashCode()
  }

  override fun toString() = z3Symbol()
}

class SymbolicEquality {

  val id = uuid++

  companion object {
    private var uuid = 1L
  }

  fun z3Symbol() = "eq$id"

  override fun equals(other: Any?): Boolean {
    return this === other
  }

  override fun hashCode(): Int {
    return id.hashCode()
  }

  override fun toString() = z3Symbol()
}

class SymbolicPacked {}

class SymbolicInfo(val ref: Reference) {
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
    val access = solution.get(fraction)
    val accessDotZero = solution.get(packFraction)
    val type = solution.get(type)
    var newLine = false

    if (access != "0") {
      str.append("acc($ref,$access) && ")
      newLine = true
    }
    if (accessDotZero != "0") {
      str.append("acc($ref.0,$accessDotZero) && ")
      newLine = true
    }
    if (type != "MungoUnknownType") {
      str.append("typeof($ref,$type)")
      newLine = true
    }
    if (newLine) {
      str.append("\n")
    }

    for ((child, info) in children) {
      info.toString(str, child, solution)
    }
  }

  override fun toString(): String {
    return "Info{ref=$ref, f=$fraction, t=$type, pf=$packFraction}"
  }
}

class SymbolicAssertionSkeleton(
  val unknownInfo: SymbolicInfo,
  val locations: Set<Reference>,
  val equalities: Set<Pair<Reference, Reference>>
) {
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

  fun impliedBy(): Set<SymbolicAssertion> = impliedBy

  val roots = mutableMapOf<Reference, SymbolicInfo>()

  init {
    for (loc in skeleton.locations) {
      prepare(loc)
    }
  }

  fun prepare(ref: Reference): SymbolicInfo {
    return when (ref) {
      is ParameterVariable,
      is LocalVariable,
      is ThisReference,
      is ClassName,
      is ReturnSpecialVar,
      is OldSpecialVar,
      is NodeRef -> {
        roots.computeIfAbsent(ref) { SymbolicInfo(it) }
      }
      is FieldAccess -> {
        val parent = prepare(ref.receiver)
        parent.children.computeIfAbsent(ref) { SymbolicInfo(it) }
      }
      is UnknownRef -> skeleton.unknownInfo
    }
  }

  operator fun get(ref: Reference): SymbolicInfo {
    return when (ref) {
      is ParameterVariable,
      is LocalVariable,
      is ThisReference,
      is ClassName,
      is ReturnSpecialVar,
      is OldSpecialVar,
      is NodeRef -> {
        roots[ref] ?: skeleton.unknownInfo // error("No info for $ref")
      }
      is FieldAccess -> {
        val parent = get(ref.receiver)
        if (parent === skeleton.unknownInfo) {
          skeleton.unknownInfo
        } else {
          parent.children[ref] ?: skeleton.unknownInfo // error("No info for $ref")
        }
      }
      is UnknownRef -> skeleton.unknownInfo
    }
  }

  fun forEach(fn: (Reference, SymbolicInfo) -> Unit) {
    for ((ref, info) in roots) {
      fn(ref, info)
      info.forEach(fn)
    }
  }

  fun toString(solution: Solution): String {
    val str = StringBuilder()
    for ((ref, info) in roots) {
      if (solution.skipRef(ref)) continue
      info.toString(str, ref, solution)
    }

    var newLine = false
    for ((a, b) in skeleton.equalities) {
      val equals = solution.equals(this, a, b).toString()
      if (equals != "false") {
        str.append("eq($a,$b)${if (equals == "true") "" else " ($equals)"} && ")
        newLine = true
      }
    }
    if (newLine) {
      str.append("\n")
    }

    return str.toString()
  }

  override fun toString(): String {
    val str = StringBuilder()
    for ((ref, info) in roots) {
      if (ref is ThisReference || ref is LocalVariable) {
        str.append(info.toString())
        for ((_, child) in info.children) {
          str.append(child.toString())
        }
      }
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
