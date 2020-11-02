package org.checkerframework.checker.mungo.assertions

import org.checkerframework.checker.mungo.analysis.*
import java.lang.StringBuilder

class SymbolicFraction {

  val id = uuid++
  val expr = Make.S.fraction(z3Symbol())

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
  val expr = Make.S.type(z3Symbol())

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

  fun toString(str: StringBuilder, ref: Reference, solution: SomeSolution) {
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
    if (type != "Unknown") {
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
  val ctxRef: OuterContextRef,
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

  private val roots = mutableMapOf<Reference, SymbolicInfo>()

  init {
    for (loc in skeleton.locations) {
      prepare(loc)
    }
  }

  fun prepare(ref: Reference): SymbolicInfo {
    return if (ref is UnknownRef) {
      skeleton.unknownInfo
    } else {
      val parent = ref.parent
      if (parent == null) {
        roots.computeIfAbsent(ref) { SymbolicInfo(it) }
      } else {
        val parentInfo = prepare(parent)
        parentInfo.children.computeIfAbsent(ref) { SymbolicInfo(it) }
      }
    }
  }

  operator fun get(ref: Reference): SymbolicInfo {
    return if (ref is UnknownRef) {
      skeleton.unknownInfo
    } else {
      val parent = ref.parent
      if (parent == null) {
        roots[ref] ?: skeleton.unknownInfo // error("No info for $ref")
      } else {
        val parentInfo = this[parent]
        if (parentInfo === skeleton.unknownInfo) {
          skeleton.unknownInfo
        } else {
          parentInfo.children[ref] ?: skeleton.unknownInfo // error("No info for $ref")
        }
      }
    }
  }

  fun forEach(fn: (Reference, SymbolicInfo) -> Unit) {
    for ((ref, info) in roots) {
      fn(ref, info)
      info.forEach(fn)
    }
  }

  fun toString(solution: SomeSolution): String {
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

  fun debug(solution: SomeSolution, middle: String) {
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
