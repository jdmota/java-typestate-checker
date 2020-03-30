package org.checkerframework.checker.mungo.typecheck

import org.checkerframework.checker.mungo.qualifiers.MungoBottom
import org.checkerframework.checker.mungo.qualifiers.MungoInternalInfo
import org.checkerframework.checker.mungo.qualifiers.MungoUnknown
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.checker.mungo.typestate.graph.states.State
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
  abstract fun isSubtype(type: MungoType): Boolean
  abstract fun leastUpperBound(type: MungoType): MungoType
  abstract fun mostSpecific(type: MungoType): MungoType?
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

  override fun leastUpperBound(type: MungoType) = MungoUnionType.create(listOf(this, type))
}

class MungoUnionType private constructor(val types: Set<MungoType>) : MungoTypeWithId() {

  init {
    map[id] = this
  }

  // invariant: types.size > 1 && UnknownType !in types && BottomType !in types && UnionType !in types

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
      return MungoUnionType(flatTypes)
    }
  }

  override fun isSubtype(type: MungoType) = when (type) {
    is MungoUnknownType -> true
    is MungoUnionType -> type.types.containsAll(types)
    else -> false
  }

  override fun mostSpecific(type: MungoType) = when (type) {
    is MungoUnknownType -> this
    is MungoUnionType -> when {
      type.types.containsAll(types) -> this
      types.containsAll(type.types) -> type
      else -> null
    }
    is MungoBottomType -> type
    else -> when {
      types.contains(type) -> type
      else -> null
    }
  }

  override fun equals(other: Any?) = when {
    this === other -> true
    other is MungoUnionType -> types == other.types
    else -> false
  }

  override fun hashCode() = types.hashCode()
  override fun toString() = "MungoUnionType$types"
}

class MungoStateType private constructor(val graph: Graph, val state: State) : MungoTypeWithId() {

  init {
    map[id] = this
  }

  companion object {
    fun create(graph: Graph, state: State) = if (state.transitions.isEmpty()) MungoEndedType.SINGLETON else MungoStateType(graph, state)
  }

  override fun isSubtype(type: MungoType) = when (type) {
    is MungoUnknownType -> true
    is MungoStateType -> graph == type.graph && state == type.state
    is MungoUnionType -> type.types.contains(this)
    else -> false
  }

  override fun mostSpecific(type: MungoType) = when (type) {
    is MungoUnknownType -> this
    is MungoStateType -> if (this == type) this else null
    is MungoUnionType -> if (type.types.contains(this)) this else null
    is MungoBottomType -> type
    else -> null
  }

  override fun equals(other: Any?) = when {
    this === other -> true
    other is MungoStateType -> graph == other.graph && state == other.state
    else -> false
  }

  override fun hashCode() = 31 * graph.hashCode() + state.name.hashCode()
  override fun toString() = "MungoStateType$state"
}

sealed class MungoTypeSingletons(private val hashCode: Int) : MungoTypeWithId() {

  override fun isSubtype(type: MungoType) = when (type) {
    is MungoUnknownType -> true
    is MungoUnionType -> type.types.contains(this)
    else -> type === this
  }

  override fun mostSpecific(type: MungoType) = when (type) {
    is MungoUnknownType -> this
    is MungoUnionType -> if (type.types.contains(this)) this else null
    is MungoBottomType -> type
    else -> if (type === this) this else null
  }

  override fun equals(other: Any?) = this === other
  override fun hashCode() = hashCode
}

class MungoMovedType private constructor() : MungoTypeSingletons(5) {

  companion object {
    val SINGLETON = MungoMovedType()
  }

  init {
    map[id] = this
  }

  override fun toString() = "MungoMovedType"
}

class MungoEndedType private constructor() : MungoTypeSingletons(4) {

  companion object {
    val SINGLETON = MungoEndedType()
  }

  init {
    map[id] = this
  }

  override fun toString() = "MungoEndedType"
}

class MungoNoProtocolType private constructor() : MungoTypeSingletons(3) {

  companion object {
    val SINGLETON = MungoNoProtocolType()
  }

  init {
    map[id] = this
  }

  override fun toString() = "MungoNoProtocolType"
}

class MungoNullType private constructor() : MungoTypeSingletons(2) {

  companion object {
    val SINGLETON = MungoNullType()
  }

  init {
    map[id] = this
  }

  override fun toString() = "MungoNullType"
}

class MungoUnknownType private constructor() : MungoType() {
  companion object {
    val SINGLETON = MungoUnknownType()
  }

  override fun buildAnnotation(env: ProcessingEnvironment): AnnotationMirror = AnnotationBuilder(env, MungoUnknown::class.java).build()
  override fun isSubtype(type: MungoType) = this === type
  override fun leastUpperBound(type: MungoType) = this
  override fun mostSpecific(type: MungoType) = type
  override fun equals(other: Any?) = this === other
  override fun hashCode() = 1
  override fun toString() = "MungoUnknownType"
}

class MungoBottomType private constructor() : MungoType() {
  companion object {
    val SINGLETON = MungoBottomType()
  }

  override fun buildAnnotation(env: ProcessingEnvironment): AnnotationMirror = AnnotationBuilder(env, MungoBottom::class.java).build()
  override fun isSubtype(type: MungoType) = true
  override fun leastUpperBound(type: MungoType) = type
  override fun mostSpecific(type: MungoType) = this
  override fun equals(other: Any?) = this === other
  override fun hashCode() = 0
  override fun toString() = "MungoBottomType"
}
