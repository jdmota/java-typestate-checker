package jatyc.core

import jatyc.core.typesystem.Subtyping
import jatyc.core.typesystem.TypeInfo
import jatyc.typestate.graph.Graph
import jatyc.typestate.graph.State
import jatyc.utils.JTCUtils

private fun unionSeq(a: JTCType, b: JTCType) = sequence {
  if (a is JTCUnionType) yieldAll(a.types) else yield(a)
  if (b is JTCUnionType) yieldAll(b.types) else yield(b)
}

private fun intersectionSeq(a: JTCType, b: JTCType) = sequence {
  if (a is JTCIntersectionType) yieldAll(a.types) else yield(a)
  if (b is JTCIntersectionType) yieldAll(b.types) else yield(b)
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
    if (type is JTCIntersectionType) yieldAll(type.types) else yield(type)
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
  return JTCIntersectionType(list.toSet())
}

sealed class JTCType {
  abstract fun format(): String

  fun isSubtype(other: JTCType) = Subtyping.isSubtype(this, other)

  open fun intersect(other: JTCType): JTCType {
    if (this === other) return this
    Subtyping.refineIntersection(this, other)?.let { return@intersect it }
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

  fun toShared(): JTCType {
    return when (this) {
      is JTCUnknownType,
      is JTCPrimitiveType,
      is JTCNullType,
      is JTCSharedType,
      is JTCBottomType -> this
      is JTCStateType -> JTCSharedType(javaType)
      is JTCUnionType -> createUnion(unionSeq(types.map { it.toShared() }))
      // Since "types" does not include union types, "toShared" will also not produce union types
      // So we do not break the pre-condition of "intersectionSeq"
      is JTCIntersectionType -> createIntersection(intersectionSeq(types.map { it.toShared() }))
      is JTCLinearArrayType -> JTCSharedType(javaType)
    }
  }

  fun toMaybeNullable(nullable: Boolean): JTCType {
    return if (nullable) this.union(JTCNullType.SINGLETON) else this
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

class JTCIntersectionType internal constructor(val types: Set<JTCType>) : JTCType() {

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
}

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

  fun isUnknown() = state == graph.getUnknownState()
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


class JTCLinearArrayType internal constructor(val javaType: JavaType, val types: List<TypeInfo>, val unknownSize: Boolean) : JTCType() {
  init {
    if (unknownSize) {
      if (types.isNotEmpty()) {
        println(types)
        JTCUtils.printStack()
        throw AssertionError("intersection invariant")
      }
    }
  }

  // fun updateTypes(updatedTypes: List<TypeInfo>) = JTCLinearArrayType(javaType, updatedTypes)

  override fun equals(other: Any?) = when {
    this === other -> true
    other is JTCLinearArrayType -> javaType == other.javaType && types == other.types && unknownSize == other.unknownSize
    else -> false
  }

  override fun hashCode() = types.hashCode()
  override fun toString() = "JTCLinearArrayType${if (unknownSize) "[?]" else "$types"}"

  private var formatCache: String? = null
  override fun format() = formatCache ?: run {
    val cache = JTCTypeFormatter.formatLinearArray(types, unknownSize)
    formatCache = cache
    cache
  }
}

private object JTCTypeFormatter {

  private fun index(t: JTCType): Int {
    return when (t) {
      is JTCUnknownType -> 1
      is JTCUnionType -> 2
      is JTCIntersectionType -> 3
      is JTCSharedType -> 4
      // is JTCNoProtocolType -> 5
      is JTCStateType -> 7
      is JTCNullType -> 8
      is JTCPrimitiveType -> 9
      is JTCBottomType -> 10
      is JTCLinearArrayType -> 11
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

  fun formatLinearArray(types: Collection<TypeInfo>, unknownSize: Boolean): String {
    return if (unknownSize) "LinearArray[?]" else "LinearArray[${types.joinToString(", "){ it.format() }}]"
  }

}
