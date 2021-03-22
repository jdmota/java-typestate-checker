package org.checkerframework.checker.jtc.typecheck

import org.checkerframework.checker.jtc.typestate.graph.Graph
import org.checkerframework.checker.jtc.typestate.graph.State
import org.checkerframework.checker.jtc.utils.JTCUtils

// To avoid the creation of new unnecessary JCTType instances
private val graphToType = mutableMapOf<Graph, JTCType>()
fun createTypeWithAllStates(graph: Graph) = graphToType.computeIfAbsent(graph) { g ->
  JTCUnionType.create(g.getAllConcreteStates().map { JTCStateType.create(graph, it) })
}

sealed class JTCType {
  abstract fun format(): String

  open fun isSubtype(other: JTCType): Boolean = isSubtype(this, other)

  open fun intersect(other: JTCType): JTCType = intersect(this, other)
  open fun union(other: JTCType) = JTCUnionType.create(listOf(this, other))

  open fun mostSpecific(other: JTCType) = when {
    this.isSubtype(other) -> this
    other.isSubtype(this) -> other
    else -> null
  }

  open fun leastUpperBound(other: JTCType) = JTCUnionType.create(listOf(this, other))

  fun replace(state1: JTCStateType, state2: JTCStateType): JTCType {
    return when (this) {
      is JTCBottomType -> this
      is JTCStateType -> if (this == state1) state2 else this
      is JTCEndedType -> this
      is JTCMovedType -> this
      is JTCNoProtocolType -> this
      is JTCNullType -> this
      is JTCObjectType -> this
      is JTCPrimitiveType -> this
      is JTCUnionType -> JTCUnionType.create(this.types.map { it.replace(state1, state2) })
      is JTCUnknownType -> this
    }
  }
}

private fun isObjectType(a: JTCType) = a is JTCStateType || a is JTCEndedType || a is JTCNoProtocolType
private fun isNotObjectType(a: JTCType) = a is JTCNullType || a is JTCPrimitiveType || a is JTCMovedType

// Returns true iff a <: b assuming that isObjectType(a)
private fun isObjectSubtype(a: JTCType, b: JTCType) = when (b) {
  is JTCUnknownType -> true
  is JTCObjectType -> true
  is JTCUnionType -> b.types.any { it == a || it == JTCObjectType.SINGLETON }
  else -> a == b
}

// pre: isNotObjectType(a)
// Returns true iff a <: b assuming that isNotObjectType(a)
private fun isNotObjectSubtype(a: JTCType, b: JTCType) = when (b) {
  is JTCUnknownType -> true
  is JTCUnionType -> b.types.any { it == a }
  else -> a == b
}

private fun isSubtype(a: JTCType, b: JTCType): Boolean = when (a) {
  is JTCUnknownType -> b is JTCUnknownType
  is JTCObjectType -> when (b) {
    is JTCUnknownType -> true
    is JTCObjectType -> true
    is JTCUnionType -> b.types.contains(JTCObjectType.SINGLETON)
    else -> false
  }
  is JTCStateType -> isObjectSubtype(a, b)
  is JTCEndedType -> isObjectSubtype(a, b)
  is JTCNoProtocolType -> isObjectSubtype(a, b)
  is JTCMovedType -> isNotObjectSubtype(a, b)
  is JTCNullType -> isNotObjectSubtype(a, b)
  is JTCPrimitiveType -> isNotObjectSubtype(a, b)
  is JTCBottomType -> true
  is JTCUnionType -> when (b) {
    is JTCUnknownType -> true
    is JTCObjectType -> a.types.all { isObjectType(it) }
    is JTCUnionType -> a.types.all { itA -> b.types.any { itB -> isSubtype(itA, itB) } }
    else -> false
  }
}

private fun intersect(a: JTCType, b: JTCType): JTCType = when (a) {
  is JTCUnknownType -> b
  is JTCObjectType -> when (b) {
    is JTCUnknownType -> a
    is JTCObjectType -> a
    is JTCUnionType -> JTCUnionType.create(b.types.map { intersect(a, it) })
    else -> if (isObjectType(b)) b else JTCBottomType.SINGLETON
  }
  is JTCStateType -> if (isObjectSubtype(a, b)) a else JTCBottomType.SINGLETON
  is JTCEndedType -> if (isObjectSubtype(a, b)) a else JTCBottomType.SINGLETON
  is JTCNoProtocolType -> if (isObjectSubtype(a, b)) a else JTCBottomType.SINGLETON
  is JTCMovedType -> if (isNotObjectSubtype(a, b)) a else JTCBottomType.SINGLETON
  is JTCNullType -> if (isNotObjectSubtype(a, b)) a else JTCBottomType.SINGLETON
  is JTCPrimitiveType -> if (isNotObjectSubtype(a, b)) a else JTCBottomType.SINGLETON
  is JTCBottomType -> a
  is JTCUnionType -> when (b) {
    is JTCUnknownType -> a
    is JTCBottomType -> b
    else -> JTCUnionType.create(a.types.map { intersect(b, it) })
  }
}

class JTCUnionType private constructor(val types: Set<JTCType>) : JTCType() {

  init {
    if (types.size <= 1) {
      JTCUtils.printStack()
      throw AssertionError("union invariant")
    }
  }

  // invariant: types.size > 1
  // invariant: types does not include UnknownType, BottomType nor UnionType
  // invariant: if ObjectType is present, subtypes of it are not

  companion object {
    fun create(types: Collection<JTCType>): JTCType {
      var flatTypes = types.flatMap {
        when (it) {
          // Ensure set does not contain UnionType
          is JTCUnionType -> it.types
          // Ensure set does not contain BottomType
          is JTCBottomType -> listOf()
          else -> listOf(it)
        }
      }.toSet() // Avoid duplicates by making it a set

      // Simplify if ObjectType is present
      if (flatTypes.contains(JTCObjectType.SINGLETON)) {
        flatTypes = flatTypes.filterNot { isObjectType(it) }.toSet()
      }

      // If set is empty, return Bottom
      if (flatTypes.isEmpty()) return JTCBottomType.SINGLETON
      // If set has only one type, return it
      if (flatTypes.size == 1) return flatTypes.first()
      // If set has Unknown, return it
      if (flatTypes.contains(JTCUnknownType.SINGLETON)) return JTCUnknownType.SINGLETON
      // Create union type
      return JTCUnionType(flatTypes)
    }
  }

  override fun equals(other: Any?) = when {
    this === other -> true
    other is JTCUnionType -> types == other.types
    else -> false
  }

  override fun hashCode() = types.hashCode()
  override fun toString() = "JTCUnionType$types"

  private var formatCache: String? = null

  override fun format() = formatCache ?: run {
    val states = types.filterIsInstance<JTCStateType>()
    val notStates = types.filterNot { it is JTCStateType }.sortedBy { it.hashCode() }
    val cache = states.plus(notStates).joinToString(" | ") { it.format() }
    formatCache = cache
    cache
  }
}

class JTCStateType private constructor(val graph: Graph, val state: State) : JTCType() {

  companion object {
    fun create(graph: Graph, state: State) = if (state.isEnd()) JTCEndedType.SINGLETON else JTCStateType(graph, state)
  }

  override fun equals(other: Any?) = when {
    this === other -> true
    other is JTCStateType -> graph == other.graph && state == other.state
    else -> false
  }

  override fun hashCode() = 31 * graph.hashCode() + state.name.hashCode()
  override fun toString() = "JTCStateType$state"
  override fun format() = "State \"${state.name}\"" // "${graph.typestateName}{${state.name}}"
}

sealed class JTCTypeSingletons(private val hashCode: Int) : JTCType() {
  override fun equals(other: Any?) = this === other
  override fun hashCode() = hashCode
}

class JTCMovedType private constructor() : JTCTypeSingletons(7) {

  companion object {
    val SINGLETON = JTCMovedType()
  }

  override fun toString() = "JTCMovedType"
  override fun format() = "Moved"
}

class JTCPrimitiveType private constructor() : JTCTypeSingletons(6) {

  companion object {
    val SINGLETON = JTCPrimitiveType()
  }

  override fun toString() = "JTCPrimitiveType"
  override fun format() = "Primitive"
}

class JTCNullType private constructor() : JTCTypeSingletons(5) {

  companion object {
    val SINGLETON = JTCNullType()
  }

  override fun toString() = "JTCNullType"
  override fun format() = "Null"
}

class JTCEndedType private constructor() : JTCTypeSingletons(4) {

  companion object {
    val SINGLETON = JTCEndedType()
  }

  override fun toString() = "JTCEndedType"
  override fun format() = "Ended"
}

class JTCNoProtocolType private constructor() : JTCTypeSingletons(3) {

  companion object {
    val SINGLETON = JTCNoProtocolType()
  }

  override fun toString() = "JTCNoProtocolType"
  override fun format() = "NoProtocol"
}

class JTCObjectType private constructor() : JTCTypeSingletons(2) {

  companion object {
    val SINGLETON = JTCObjectType()
  }

  override fun toString() = "JTCObjectType"
  override fun format() = "Object"
}

class JTCUnknownType private constructor() : JTCType() {
  companion object {
    val SINGLETON = JTCUnknownType()
  }

  override fun isSubtype(other: JTCType) = this === other
  override fun intersect(other: JTCType) = other
  override fun mostSpecific(other: JTCType) = other
  override fun leastUpperBound(other: JTCType) = this
  override fun equals(other: Any?) = this === other
  override fun hashCode() = 1
  override fun toString() = "JTCUnknownType"
  override fun format() = "Unknown"
}

class JTCBottomType private constructor() : JTCType() {
  companion object {
    val SINGLETON = JTCBottomType()
  }

  override fun isSubtype(other: JTCType) = true
  override fun intersect(other: JTCType) = this
  override fun mostSpecific(other: JTCType) = this
  override fun leastUpperBound(other: JTCType) = other
  override fun equals(other: Any?) = this === other
  override fun hashCode() = 0
  override fun toString() = "JTCBottomType"
  override fun format() = "Bottom"
}
