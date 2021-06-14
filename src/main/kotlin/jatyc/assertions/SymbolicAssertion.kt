package jatyc.assertions

import java.lang.StringBuilder

class SymbolicFraction(val info: SymbolicInfo) {

  val id = uuid++
  val expr = Make.S.fraction(this)

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

class SymbolicType(val info: SymbolicInfo) {

  val id = uuid++
  val expr = Make.S.type(this)

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

private const val DEBUG = false

class SymbolicInfo(val ref: Reference, private val assertion: SymbolicAssertion?) {
  val fraction = SymbolicFraction(this) // access(x, f1)
  val type = SymbolicType(this) // typeof(x, t1)

  // val packed = SymbolicPacked() // packed(x) or unpacked(x)
  val packFraction = SymbolicFraction(this) // access(x.0, f2)
  val children = mutableMapOf<Reference, SymbolicInfo>()

  fun forEach(fn: (Reference, SymbolicInfo) -> Unit) {
    for ((ref, info) in children) {
      fn(ref, info)
      info.forEach(fn)
    }
  }

  fun debugWhere() = "$ref in ${assertion?.where}"

  fun toString(str: StringBuilder, ref: Reference, solution: SomeSolution) {
    val access = solution.get(fraction)
    val accessDotZero = solution.get(packFraction)
    val type = solution.get(type)

    if (DEBUG) {
      val hasAccess = access != "0"
      val hasDotZeroAccess = accessDotZero != "0"
      val hasRelevantType = type != "Unknown"
      val strings = mutableListOf<String>()

      if (hasAccess) {
        strings.add("access($ref,$access)")
      }
      if (hasDotZeroAccess) {
        strings.add("access($ref.0,$accessDotZero)")
      }
      if (hasRelevantType) {
        strings.add("typeof($ref,$type)")
      }

      if (strings.isNotEmpty()) {
        str.appendLine("// ${strings.joinToString(" && ")}") // $\wedge$
      }
    } else {
      val hasAccess = access != "0"
      val hasDotZeroAccess = accessDotZero != "0"
      val hasRelevantType =
        type != "Unknown" &&
          type != "Object" &&
          type != "Object | Null" &&
          (ref !is ReturnSpecialVar || type != "Primitive") &&
          (ref !is NodeRef || type != "Primitive")
      val showAccesses = (hasRelevantType || (ref !is ReturnSpecialVar && ref !is NodeRef))
      val strings = mutableListOf<String>()

      if (hasAccess && showAccesses) {
        strings.add("access($ref,$access)")
      }
      if (hasDotZeroAccess && showAccesses) {
        strings.add("access($ref.0,$accessDotZero)")
      }
      if (hasRelevantType) {
        strings.add("typeof($ref,$type)")
      }

      if (strings.isNotEmpty()) {
        str.appendLine("// ${strings.joinToString(" && ")}") // $\wedge$
      }
    }

    for ((child, info) in children) {
      info.toString(str, child, solution)
    }
  }

  override fun toString(): String {
    return "Info{ref=$ref, f=$fraction, pf=$packFraction, t=$type}"
  }
}

class SymbolicAssertionSkeleton(
  val unknownInfo: SymbolicInfo,
  val ctxRef: OuterContextRef,
  val locations: Set<Reference>,
  val equalities: PossibleEqualitiesTracker
) {
  val allEqualities = equalities.getAll()

  fun getPossibleEq(ref: Reference) = equalities.aliases(ref)

  fun isPossibleEq(a: Reference, b: Reference) = allEqualities.contains(Pair(a, b))

  fun create() = SymbolicAssertion(this)
}

class SymbolicAssertion(val skeleton: SymbolicAssertionSkeleton, var where: String? = null) {

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
        roots.computeIfAbsent(ref) { SymbolicInfo(it, this) }
      } else {
        val parentInfo = prepare(parent)
        parentInfo.children.computeIfAbsent(ref) { SymbolicInfo(it, this) }
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

    for ((a, b) in skeleton.allEqualities) {
      val equals = solution.equals(this, a, b)
      if (equals != "false" && equals != "0") {
        str.appendLine("// eq($a,$b)${if (equals == "true" || equals == "1") "" else " ($equals)"}")
      }
    }

    return str.toString()
  }

  override fun toString(): String {
    val str = StringBuilder()
    for ((ref, info) in roots) {
      if (ref is ThisReference || ref is LocalVariable || ref is ParameterVariable) {
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
  val postElse: SymbolicAssertion,
  val where: String?
) {

  init {
    if (where != null) {
      preThen.where = "pre($where)"
      preElse.where = "pre($where)"
      postThen.where = "post($where)"
      postElse.where = "post($where)"
    }
  }

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
