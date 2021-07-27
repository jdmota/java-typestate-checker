package jatyc.core

import jatyc.typestate.graph.Graph
import jatyc.typestate.graph.State
import jatyc.utils.JTCUtils

private fun unionSeq(a: JTCType, b: JTCType) = sequence {
  if (a is JTCUnionType) yieldAll(a.types) else yield(a)
  if (b is JTCUnionType) yieldAll(b.types) else yield(b)
}

private fun intersectionSeq(a: JTCType, b: JTCType) = sequence {
  /*if (a is JTCIntersectionType) yieldAll(a.types) else*/ yield(a)
  /*if (b is JTCIntersectionType) yieldAll(b.types) else*/ yield(b)
}

// Sequence does not produce union types
private fun unionSeq(list: Collection<JTCType>) = sequence {
  for (type in list) {
    if (type is JTCUnionType) yieldAll(type.types) else yield(type)
  }
}

// Sequence does not produce intersection or union types assuming "list" does not contain union types
private fun intersectionSeq(list: Collection<JTCType>) = sequence {
  for (type in list) {
    /*if (type is JTCIntersectionType) yieldAll(type.types) else*/ yield(type)
  }
}

// Assuming "sequence" does not contain unions
private fun createUnion(sequence: Sequence<JTCType>): JTCType {
  val list = mutableListOf<JTCType>()
  for (next in sequence) {
    if (list.none { next.isSubtype(it) }) {
      list.removeAll { it.isSubtype(next) }
      list.add(next)
    }
  }
  // If list is empty, return Bottom
  if (list.isEmpty()) return JTCBottomType.SINGLETON
  // If list has only one type, return it
  if (list.size == 1) return list.first()
  // Create union type
  return JTCUnionType(list.toSet())
}

// Assuming "iterator" does not contain unions or intersections
private fun createIntersection(sequence: Sequence<JTCType>): JTCType {
  val list = mutableListOf<JTCType>()
  for (next in sequence) {
    if (list.none { it.isSubtype(next) }) {
      list.removeAll { next.isSubtype(it) }
      list.add(next)
    }
  }
  // If list is empty, return Unknown
  if (list.isEmpty()) return JTCUnknownType.SINGLETON
  // If list has only one type, return it
  if (list.size == 1) return list.first()
  // Create upper bound
  return JTCUnionType(list.toSet())
}

private fun areExclusive(a: JTCType, b: JTCType): Boolean {
  return when (a) {
    // is JTCNoProtocolType -> b is JTCPrimitiveType || b is JTCNullType || b is JTCSharedType || ((b is JTCUnknownStateType || b is JTCStateType) && a.exact)
    is JTCUnknownStateType,
    is JTCStateType -> b is JTCPrimitiveType || b is JTCNullType || b is JTCSharedType /*|| (b is JTCNoProtocolType && b.exact)*/
    is JTCSharedType -> b is JTCPrimitiveType || b is JTCNullType || /*b is JTCNoProtocolType ||*/ b is JTCUnknownStateType || b is JTCStateType
    is JTCPrimitiveType -> b is JTCNullType || b is JTCSharedType || /*b is JTCNoProtocolType ||*/ b is JTCUnknownStateType || b is JTCStateType
    is JTCNullType -> b is JTCPrimitiveType || b is JTCSharedType || /*b is JTCNoProtocolType ||*/ b is JTCUnknownStateType || b is JTCStateType
    else -> false
  }
}

private fun attemptDowncast(a: JTCStateType, b: JTCUnknownStateType): JTCType? {
  if (b.javaType.isSubtype(a.javaType)) {
    if (a.state == a.graph.getInitialState()) {
      return JTCStateType(b.javaType, b.graph, b.graph.getInitialState())
    }
    if (a.state.isEnd()) {
      return JTCStateType(b.javaType, b.graph, b.graph.getEndState())
    }
  }
  return null
}

sealed class JTCType {
  abstract fun format(): String

  fun isSubtype(other: JTCType): Boolean {
    return Subtyping.subtype(this, other)
  }

  open fun intersect(other: JTCType): JTCType {
    if (this === other) return this
    if (areExclusive(this, other)) return JTCBottomType.SINGLETON
    if (this is JTCStateType && other is JTCUnknownStateType) {
      attemptDowncast(this, other)?.let { return@intersect it }
    }
    if (this is JTCUnknownStateType && other is JTCStateType) {
      attemptDowncast(other, this)?.let { return@intersect it }
    }
    return when {
      // We need to ensure that there are no unions in intersections
      this is JTCUnionType -> createUnion(unionSeq(this.types.map { it.intersect(other) }))
      other is JTCUnionType -> createUnion(unionSeq(other.types.map { it.intersect(this) }))
      // Since intersections do not contain unions (nor intersections) and since "this" and "other" are not unions
      // This sequence will not produce unions nor intersections
      else -> createIntersection(intersectionSeq(this, other))
    }
  }

  open fun union(other: JTCType): JTCType {
    return if (this === other) {
      this
    } else {
      createUnion(unionSeq(this, other))
    }
  }

  fun requiresLinear(): Boolean {
    return when (this) {
      is JTCUnknownType -> false
      is JTCSharedType -> false
      is JTCPrimitiveType,
      is JTCNullType,
      // is JTCNoProtocolType,
      is JTCUnknownStateType,
      is JTCStateType,
      is JTCBottomType -> true
      is JTCUnionType -> types.all { it.requiresLinear() }
      // is JTCIntersectionType -> types.any { it.requiresLinear() }
    }
  }

  fun toShared(): JTCType {
    return when (this) {
      is JTCUnknownType,
      is JTCPrimitiveType,
      is JTCNullType,
      is JTCSharedType,
      is JTCBottomType -> this
      // is JTCNoProtocolType -> JTCSharedType(javaType)
      is JTCUnknownStateType -> JTCSharedType(javaType)
      is JTCStateType -> JTCSharedType(javaType)
      is JTCUnionType -> createUnion(unionSeq(types.map { it.toShared() }))
      // Since "types" does not include union types, "toShared" will also not produce union types
      // So we do not break the pre-condition of "intersectionSeq"
      // is JTCIntersectionType -> createIntersection(intersectionSeq(types.map { it.toShared() }))
    }
  }

  fun toMaybeNullable(nullable: Boolean): JTCType {
    return if (nullable) this.union(JTCNullType.SINGLETON) else this
  }

  fun replace(state1: JTCStateType, state2: JTCStateType): JTCType {
    return when (this) {
      is JTCUnknownType,
      is JTCPrimitiveType,
      is JTCNullType,
      is JTCSharedType,
      is JTCBottomType -> this
      // is JTCNoProtocolType -> this
      is JTCUnknownStateType -> this
      is JTCStateType -> if (this == state1) state2 else this
      is JTCUnionType -> createUnion(types.map { it.replace(state1, state2) })
      // is JTCIntersectionType -> createIntersection(types.map { it.replace(state1, state2) })
    }
  }

  companion object {
    fun createUnion(list: Collection<JTCType>) = createUnion(unionSeq(list))
    fun createIntersection(list: Collection<JTCType>) = list.fold<JTCType, JTCType>(JTCUnknownType.SINGLETON) { acc, it -> acc.intersect(it) }
  }
}

class JTCUnionType internal constructor(val types: Set<JTCType>) : JTCType() {

  init {
    if (types.size <= 1) {
      println(types)
      JTCUtils.printStack()
      throw AssertionError("union invariant")
    }
  }

  // invariant: types.size > 1
  // invariant: types does not include UnknownType, BottomType nor UnionType

  override fun equals(other: Any?) = when {
    this === other -> true
    other is JTCUnionType -> types == other.types
    else -> false
  }

  override fun hashCode() = types.hashCode()
  override fun toString() = "JTCUnionType$types"

  private var formatCache: String? = null
  override fun format() = formatCache ?: run {
    val cache = JTCTypeFormatter.formatUnion(types)
    formatCache = cache
    cache
  }
}

/*class JTCIntersectionType internal constructor(val types: Set<JTCType>) : JTCType() {

  init {
    if (types.size <= 1) {
      println(types)
      JTCUtils.printStack()
      throw AssertionError("intersection invariant")
    }
  }

  // invariant: types.size > 1
  // invariant: types does not include UnknownType, BottomType, UnionType nor IntersectionType

  override fun equals(other: Any?) = when {
    this === other -> true
    other is JTCIntersectionType -> types == other.types
    else -> false
  }

  override fun hashCode() = types.hashCode()
  override fun toString() = "JTCIntersectionType$types"

  private var formatCache: String? = null
  override fun format() = formatCache ?: run {
    val cache = JTCTypeFormatter.formatIntersection(types)
    formatCache = cache
    cache
  }
}*/

class JTCStateType internal constructor(val javaType: JavaType, val graph: Graph, val state: State) : JTCType() {
  override fun equals(other: Any?) = when {
    this === other -> true
    other is JTCStateType -> javaType == other.javaType && graph == other.graph && state == other.state
    else -> false
  }

  override fun hashCode(): Int {
    var result = javaType.hashCode()
    result = 31 * result + graph.hashCode()
    result = 31 * result + state.hashCode()
    return result
  }

  override fun toString() = "JTCStateType{$javaType, ${graph.typestateName}, $state}"
  override fun format() = "State{$javaType, ${state.format()}}"
}

class JTCUnknownStateType internal constructor(val javaType: JavaType, val graph: Graph) : JTCType() {

  override fun equals(other: Any?) = when {
    this === other -> true
    other is JTCUnknownStateType -> javaType == other.javaType && graph == other.graph
    else -> false
  }

  override fun hashCode(): Int {
    var result = javaType.hashCode()
    result = 31 * result + graph.hashCode()
    return result
  }

  override fun toString() = "JTCUnknownStateType{${javaType}}"
  override fun format() = "State{$javaType, ?}"
}

/*class JTCNoProtocolType internal constructor(val javaType: JavaType, isActualType: Boolean) : JTCType() {

  val exact = isActualType || javaType.isFinal()

  override fun equals(other: Any?) = when {
    this === other -> true
    other is JTCNoProtocolType -> javaType == other.javaType && exact == other.exact
    else -> false
  }

  override fun hashCode(): Int {
    return javaType.hashCode()
  }

  override fun isSubtype(other: JTCType): Boolean {
    return when (other) {
      is JTCUnknownType -> true
      is JTCUnionType -> other.types.any { this.isSubtype(it) }
      is JTCIntersectionType -> other.types.all { this.isSubtype(it) }
      is JTCNoProtocolType -> if (other.exact) this == other else javaType.isSubtype(other.javaType)
      else -> false
    }
  }

  override fun toString() = "JTCNoProtocolType{$javaType, exact=$exact}"
  override fun format() = "NoProtocol{$javaType, exact=$exact}"
}*/

class JTCPrimitiveType internal constructor(val javaType: JavaType) : JTCType() {

  override fun equals(other: Any?) = when {
    this === other -> true
    other is JTCPrimitiveType -> javaType == other.javaType
    else -> false
  }

  override fun hashCode(): Int {
    return javaType.hashCode()
  }

  override fun toString() = "JTCPrimitiveType{${javaType}}"
  override fun format() = "Primitive{${javaType}}"
}

class JTCSharedType internal constructor(val javaType: JavaType) : JTCType() {
  override fun equals(other: Any?) = when {
    this === other -> true
    other is JTCSharedType -> javaType == other.javaType
    else -> false
  }

  override fun hashCode(): Int {
    return javaType.hashCode()
  }

  override fun toString() = "JTCSharedType{${javaType}}"
  override fun format() = "Shared{${javaType}}"
}

sealed class JTCTypeSingletons(private val hashCode: Int) : JTCType() {
  override fun equals(other: Any?) = this === other
  override fun hashCode() = hashCode
}

class JTCUnknownType private constructor() : JTCTypeSingletons(1) {
  companion object {
    val SINGLETON = JTCUnknownType()
  }

  override fun union(other: JTCType): JTCType {
    return this
  }

  override fun intersect(other: JTCType): JTCType {
    return other
  }

  override fun toString() = "JTCUnknownType"
  override fun format() = "Unknown"
}

class JTCNullType private constructor() : JTCTypeSingletons(2) {
  companion object {
    val SINGLETON = JTCNullType()
  }

  override fun toString() = "JTCNullType"
  override fun format() = "Null"
}

class JTCBottomType private constructor() : JTCTypeSingletons(3) {
  companion object {
    val SINGLETON = JTCBottomType()
  }

  override fun union(other: JTCType): JTCType {
    return other
  }

  override fun intersect(other: JTCType): JTCType {
    return this
  }

  override fun toString() = "JTCBottomType"
  override fun format() = "Bottom"
}

private object JTCTypeFormatter {

  private fun index(t: JTCType): Int {
    return when (t) {
      is JTCUnknownType -> 1
      is JTCUnionType -> 2
      // is JTCIntersectionType -> 3
      is JTCSharedType -> 4
      // is JTCNoProtocolType -> 5
      is JTCUnknownStateType -> 6
      is JTCStateType -> 7
      is JTCNullType -> 8
      is JTCPrimitiveType -> 9
      is JTCBottomType -> 10
    }
  }

  private object JTCTypeComparator : Comparator<JTCType> {
    override fun compare(t1: JTCType, t2: JTCType): Int {
      val i1 = index(t1)
      val i2 = index(t2)
      return if (i1 == i2) {
        when {
          // t1 is JTCIntersectionType && t2 is JTCIntersectionType -> t1.types.size - t2.types.size
          t1 is JTCSharedType && t2 is JTCSharedType -> t1.javaType.toString().compareTo(t2.javaType.toString())
          // t1 is JTCNoProtocolType && t2 is JTCNoProtocolType -> t1.javaType.toString().compareTo(t2.javaType.toString())
          t1 is JTCUnknownStateType && t2 is JTCUnknownStateType -> t1.javaType.toString().compareTo(t2.javaType.toString())
          t1 is JTCStateType && t2 is JTCStateType -> {
            val c = t1.javaType.toString().compareTo(t2.javaType.toString())
            if (c == 0) {
              when {
                t1.state.name == "end" -> 1
                t2.state.name == "end" -> -1
                else -> t1.state.name.compareTo(t2.state.name)
              }
            } else c
          }
          else -> 0
        }
      } else {
        i1 - i2
      }
    }
  }

  fun formatUnion(types: Collection<JTCType>): String {
    return types.sortedWith(JTCTypeComparator).joinToString(" | ") { it.format() }
  }

  fun formatIntersection(types: Collection<JTCType>): String {
    return "(${types.sortedWith(JTCTypeComparator).joinToString(" & ") { it.format() }})"
  }

}
