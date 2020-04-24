package org.checkerframework.checker.mungo.typecheck

import org.checkerframework.checker.mungo.qualifiers.MungoBottom
import org.checkerframework.checker.mungo.qualifiers.MungoInternalInfo
import org.checkerframework.checker.mungo.qualifiers.MungoUnknown
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.checker.mungo.typestate.graph.State
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.javacutil.AnnotationBuilder
import org.checkerframework.javacutil.AnnotationUtils
import javax.annotation.processing.ProcessingEnvironment
import javax.lang.model.element.AnnotationMirror

// pre: annotation is @MungoInternalInfo
fun getTypeFromAnnotation(annotation: AnnotationMirror): MungoType {
  if (AnnotationUtils.areSameByName(annotation, MungoUtils.mungoInternalInfoName)) {
    val id = AnnotationUtils.getElementValue(annotation, "id", java.lang.Long::class.java, false)
    return map[id.toLong()]!!
  }
  throw AssertionError("getTypeFromAnnotation")
}

// To avoid the creation of new unnecessary MungoType instances
private val graphToType = mutableMapOf<Graph, MungoType>()
fun createTypeWithAllStates(graph: Graph) = graphToType.computeIfAbsent(graph) { g ->
  MungoUnionType.create(g.getAllConcreteStates().map { MungoStateType.create(graph, it) })
}

sealed class MungoType {
  abstract fun buildAnnotation(env: ProcessingEnvironment): AnnotationMirror
  abstract fun isSubtype(other: MungoType): Boolean
  abstract fun intersect(other: MungoType): MungoType
  abstract fun mostSpecific(other: MungoType): MungoType?
  abstract fun leastUpperBound(other: MungoType): MungoType
  abstract fun format(): String
}

private var uuid = 0L
private val map = mutableMapOf<Long, MungoType>()

// These types seat between Unknown and Bottom
sealed class MungoTypeWithId : MungoType() {

  val id: Long = uuid++

  override fun buildAnnotation(env: ProcessingEnvironment): AnnotationMirror {
    val builder = AnnotationBuilder(env, MungoInternalInfo::class.java)
    builder.setValue("id", id)
    return builder.build()
  }

  override fun isSubtype(other: MungoType): Boolean = isSubtype(this, other)

  override fun intersect(other: MungoType): MungoType = intersect(this, other)

  override fun mostSpecific(other: MungoType) = when {
    this.isSubtype(other) -> this
    other.isSubtype(this) -> other
    else -> null
  }

  override fun leastUpperBound(other: MungoType) = MungoUnionType.create(listOf(this, other))
}

private fun isObjectType(a: MungoType) = a is MungoStateType || a is MungoEndedType || a is MungoNoProtocolType
private fun isNotObjectType(a: MungoType) = a is MungoNullType || a is MungoPrimitiveType || a is MungoMovedType

// pre: isObjectType(a)
private fun isObjectSubtype(a: MungoType, b: MungoType) = when (b) {
  is MungoUnknownType -> true
  is MungoObjectType -> true
  is MungoUnionType -> b.types.any { it == a || it == MungoObjectType.SINGLETON }
  else -> a == b
}

// pre: isNotObjectType(a)
private fun isNotObjectSubtype(a: MungoType, b: MungoType) = when (b) {
  is MungoUnknownType -> true
  is MungoUnionType -> b.types.any { it == a }
  else -> a == b
}

private fun isSubtype(a: MungoType, b: MungoType): Boolean = when (a) {
  is MungoUnknownType -> b is MungoUnknownType
  is MungoObjectType -> when (b) {
    is MungoUnknownType -> true
    is MungoObjectType -> true
    is MungoUnionType -> b.types.contains(MungoObjectType.SINGLETON)
    else -> false
  }
  is MungoStateType -> isObjectSubtype(a, b)
  is MungoEndedType -> isObjectSubtype(a, b)
  is MungoNoProtocolType -> isObjectSubtype(a, b)
  is MungoMovedType -> isNotObjectSubtype(a, b)
  is MungoNullType -> isNotObjectSubtype(a, b)
  is MungoPrimitiveType -> isNotObjectSubtype(a, b)
  is MungoBottomType -> true
  is MungoUnionType -> when (b) {
    is MungoUnknownType -> true
    is MungoObjectType -> a.types.all { isObjectType(it) }
    is MungoUnionType -> a.types.all { itA -> b.types.any { itB -> isSubtype(itA, itB) } }
    else -> false
  }
}

private fun intersect(a: MungoType, b: MungoType): MungoType = when (a) {
  is MungoUnknownType -> b
  is MungoObjectType -> when (b) {
    is MungoUnknownType -> a
    is MungoUnionType -> MungoUnionType.create(b.types.map { intersect(a, it) })
    else -> if (isObjectType(b)) b else MungoBottomType.SINGLETON
  }
  is MungoStateType -> if (isObjectSubtype(a, b)) a else MungoBottomType.SINGLETON
  is MungoEndedType -> if (isObjectSubtype(a, b)) a else MungoBottomType.SINGLETON
  is MungoNoProtocolType -> if (isObjectSubtype(a, b)) a else MungoBottomType.SINGLETON
  is MungoMovedType -> if (isNotObjectSubtype(a, b)) a else MungoBottomType.SINGLETON
  is MungoNullType -> if (isNotObjectSubtype(a, b)) a else MungoBottomType.SINGLETON
  is MungoPrimitiveType -> if (isNotObjectSubtype(a, b)) a else MungoBottomType.SINGLETON
  is MungoBottomType -> a
  is MungoUnionType -> when (b) {
    is MungoUnknownType -> a
    is MungoBottomType -> b
    else -> MungoUnionType.create(a.types.map { intersect(b, it) })
  }
}

class MungoUnionType private constructor(val types: Set<MungoType>) : MungoTypeWithId() {

  init {
    map[id] = this
    if (types.isEmpty()) {
      MungoUtils.printStack()
      throw AssertionError("union invariant")
    }
  }

  // invariant: types.size > 1
  // invariant: types does not include UnknownType, BottomType nor UnionType
  // invariant: if ObjectType is present, subtypes of it are not

  companion object {
    fun create(types: Collection<MungoType>): MungoType {
      val flatTypes = types.flatMap {
        when (it) {
          // Ensure set does not contain UnionType
          is MungoUnionType -> it.types
          // Ensure set does not contain BottomType
          is MungoBottomType -> listOf()
          else -> listOf(it)
        }
      }.toSet() // Avoid duplicates by making it a set
      // Ensure set is not empty
      if (flatTypes.isEmpty()) return MungoBottomType.SINGLETON
      // Ensure set has size > 1
      if (flatTypes.size == 1) return flatTypes.first()
      // Ensure set does not contain UnknownType
      if (flatTypes.contains(MungoUnknownType.SINGLETON)) return MungoUnknownType.SINGLETON
      // Simplify if ObjectType is present
      if (flatTypes.contains(MungoObjectType.SINGLETON)) {
        return MungoUnionType(flatTypes.filterNot { isObjectType(it) }.toSet())
      }
      return MungoUnionType(flatTypes)
    }
  }

  override fun equals(other: Any?) = when {
    this === other -> true
    other is MungoUnionType -> types == other.types
    else -> false
  }

  override fun hashCode() = types.hashCode()
  override fun toString() = "MungoUnionType$types"

  private var formatCache: String? = null

  override fun format() = formatCache ?: run {
    val states = types.filterIsInstance<MungoStateType>()
    val notStates = types.filterNot { it is MungoStateType }

    val map = mutableMapOf<Graph, MutableList<MungoStateType>>()
    for (state in states) map.computeIfAbsent(state.graph) { mutableListOf() }.add(state)

    val cache = map.entries.map { (graph, types) ->
      "${graph.typestateName}{${types.joinToString("|") { it.state.name }}}"
    }.plus(notStates.map { it.format() }).joinToString(" | ")

    formatCache = cache
    cache
  }
}

class MungoStateType private constructor(val graph: Graph, val state: State) : MungoTypeWithId() {

  init {
    map[id] = this
  }

  companion object {
    fun create(graph: Graph, state: State) = if (state.transitions.isEmpty()) MungoEndedType.SINGLETON else MungoStateType(graph, state)
  }

  override fun equals(other: Any?) = when {
    this === other -> true
    other is MungoStateType -> graph == other.graph && state == other.state
    else -> false
  }

  override fun hashCode() = 31 * graph.hashCode() + state.name.hashCode()
  override fun toString() = "MungoStateType$state"
  override fun format() = "${graph.typestateName}{${state.name}}"
}

sealed class MungoTypeSingletons(private val hashCode: Int) : MungoTypeWithId() {
  override fun equals(other: Any?) = this === other
  override fun hashCode() = hashCode
}

class MungoObjectType private constructor() : MungoTypeSingletons(7) {

  companion object {
    val SINGLETON = MungoObjectType()
  }

  init {
    map[id] = this
  }

  override fun toString() = "MungoObjectType"
  override fun format() = "Object"
}

class MungoEndedType private constructor() : MungoTypeSingletons(6) {

  companion object {
    val SINGLETON = MungoEndedType()
  }

  init {
    map[id] = this
  }

  override fun toString() = "MungoEndedType"
  override fun format() = "Ended"
}

class MungoNoProtocolType private constructor() : MungoTypeSingletons(5) {

  companion object {
    val SINGLETON = MungoNoProtocolType()
  }

  init {
    map[id] = this
  }

  override fun toString() = "MungoNoProtocolType"
  override fun format() = "NoProtocol"
}

class MungoMovedType private constructor() : MungoTypeSingletons(4) {

  companion object {
    val SINGLETON = MungoMovedType()
  }

  init {
    map[id] = this
  }

  override fun toString() = "MungoMovedType"
  override fun format() = "Moved"
}

class MungoPrimitiveType private constructor() : MungoTypeSingletons(3) {

  companion object {
    val SINGLETON = MungoPrimitiveType()
  }

  init {
    map[id] = this
  }

  override fun toString() = "MungoPrimitiveType"
  override fun format() = "Primitive"
}

class MungoNullType private constructor() : MungoTypeSingletons(2) {

  companion object {
    val SINGLETON = MungoNullType()
  }

  init {
    map[id] = this
  }

  override fun toString() = "MungoNullType"
  override fun format() = "Null"
}

class MungoUnknownType private constructor() : MungoType() {
  companion object {
    val SINGLETON = MungoUnknownType()
  }

  override fun buildAnnotation(env: ProcessingEnvironment): AnnotationMirror = AnnotationBuilder(env, MungoUnknown::class.java).build()
  override fun isSubtype(other: MungoType) = this === other
  override fun intersect(other: MungoType) = other
  override fun mostSpecific(other: MungoType) = other
  override fun leastUpperBound(other: MungoType) = this
  override fun equals(other: Any?) = this === other
  override fun hashCode() = 1
  override fun toString() = "MungoUnknownType"
  override fun format() = "Unknown"
}

class MungoBottomType private constructor() : MungoType() {
  companion object {
    val SINGLETON = MungoBottomType()
  }

  override fun buildAnnotation(env: ProcessingEnvironment): AnnotationMirror = AnnotationBuilder(env, MungoBottom::class.java).build()
  override fun isSubtype(other: MungoType) = true
  override fun intersect(other: MungoType) = this
  override fun mostSpecific(other: MungoType) = this
  override fun leastUpperBound(other: MungoType) = other
  override fun equals(other: Any?) = this === other
  override fun hashCode() = 0
  override fun toString() = "MungoBottomType"
  override fun format() = "Bottom"
}
