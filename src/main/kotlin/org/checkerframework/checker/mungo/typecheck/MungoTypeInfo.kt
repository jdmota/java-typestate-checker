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

// To avoid the creation of new unnecessary MungoConcreteType instances
private val graphToType = mutableMapOf<Graph, MungoConcreteType>()
fun createTypeWithAllStates(graph: Graph): MungoConcreteType {
  return graphToType.computeIfAbsent(graph) { MungoConcreteType(it, it.getAllConcreteStates()) }
}

sealed class MungoType {
  abstract fun buildAnnotation(env: ProcessingEnvironment): AnnotationMirror
  abstract fun isSubtype(type: MungoType): Boolean
  abstract fun leastUpperBound(type: MungoType): MungoType
  abstract fun mostSpecific(type: MungoType): MungoType?
}

private var uuid = 0L
private val map = mutableMapOf<Long, MungoType>()

// Type information contains a set of possible states
// And the graph where those states belong
class MungoConcreteType(val graph: Graph, val states: Set<State>) : MungoType() {

  val id: Long = uuid++

  init {
    map[id] = this
    // TODO remove this
    when {
      id in 2000..2005 -> {
        println("\n-----$id------")
        println(graph.file)
        println(states)
      }
      id in 3500..3505 -> {
        println("\n-----$id------")
        println(graph.file)
        println(states)
      }
      id > 5000 -> {
        println("\n-----$id------")
        println(graph.file)
        println(states)
        throw RuntimeException("NOOOOO")
      }
    }
  }

  override fun buildAnnotation(env: ProcessingEnvironment): AnnotationMirror {
    val builder = AnnotationBuilder(env, MungoInternalInfo::class.java)
    builder.setValue("id", id)
    return builder.build()
  }

  override fun isSubtype(type: MungoType): Boolean {
    return when (type) {
      is MungoBottomType -> false
      is MungoNullType -> false
      is MungoConcreteType -> graph == type.graph && type.states.containsAll(states)
      is MungoUnknownType -> true
    }
  }

  override fun leastUpperBound(type: MungoType): MungoType {
    return when (type) {
      is MungoBottomType -> this
      is MungoNullType -> MungoUnknownType.SINGLETON
      is MungoConcreteType -> if (graph == type.graph) {
        when {
          states.containsAll(type.states) -> this
          type.states.containsAll(this.states) -> type
          else -> {
            val set = mutableSetOf<State>()
            set.addAll(states)
            set.addAll(type.states)
            MungoConcreteType(graph, set)
          }
        }
      } else MungoUnknownType.SINGLETON
      is MungoUnknownType -> MungoUnknownType.SINGLETON
    }
  }

  override fun mostSpecific(type: MungoType): MungoType? {
    return when (type) {
      is MungoBottomType -> MungoBottomType.SINGLETON
      is MungoNullType -> null
      is MungoConcreteType -> if (graph == type.graph) {
        when {
          states.containsAll(type.states) -> type
          type.states.containsAll(states) -> this
          else -> null
        }
      } else null
      is MungoUnknownType -> this
    }
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other is MungoConcreteType) return graph == other.graph && states == other.states
    return false
  }

  override fun hashCode(): Int {
    var result = graph.hashCode()
    result = 31 * result + states.size // Faster than states.hashCode()
    return result
  }

  override fun toString(): String {
    return "MungoConcreteType$states";
  }

}

class MungoNullType private constructor() : MungoType() {

  companion object {
    val SINGLETON = MungoNullType()
  }

  val id: Long = uuid++

  init {
    map[id] = this
  }

  override fun buildAnnotation(env: ProcessingEnvironment): AnnotationMirror {
    val builder = AnnotationBuilder(env, MungoInternalInfo::class.java)
    builder.setValue("id", id)
    return builder.build()
  }

  override fun isSubtype(type: MungoType): Boolean {
    return type is MungoNullType || type is MungoUnknownType
  }

  override fun leastUpperBound(type: MungoType): MungoType {
    return when (type) {
      is MungoBottomType -> this
      is MungoNullType -> this
      is MungoConcreteType -> MungoUnknownType.SINGLETON
      is MungoUnknownType -> MungoUnknownType.SINGLETON
    }
  }

  override fun mostSpecific(type: MungoType): MungoType? {
    return when (type) {
      is MungoBottomType -> type
      is MungoNullType -> type
      is MungoConcreteType -> null
      is MungoUnknownType -> this
    }
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    return other is MungoNullType
  }

  override fun hashCode(): Int {
    return 2
  }

  override fun toString(): String {
    return "MungoNullType"
  }

}

class MungoUnknownType private constructor() : MungoType() {

  companion object {
    val SINGLETON = MungoUnknownType()
  }

  override fun buildAnnotation(env: ProcessingEnvironment): AnnotationMirror {
    val builder = AnnotationBuilder(env, MungoUnknown::class.java)
    return builder.build()
  }

  override fun isSubtype(type: MungoType): Boolean {
    return type is MungoUnknownType
  }

  override fun leastUpperBound(type: MungoType): MungoType {
    return this
  }

  override fun mostSpecific(type: MungoType): MungoType? {
    return type
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    return other is MungoUnknownType
  }

  override fun hashCode(): Int {
    return 1
  }

  override fun toString(): String {
    return "MungoUnknownType"
  }

}

class MungoBottomType private constructor() : MungoType() {

  companion object {
    val SINGLETON = MungoBottomType()
  }

  override fun buildAnnotation(env: ProcessingEnvironment): AnnotationMirror {
    val builder = AnnotationBuilder(env, MungoBottom::class.java)
    return builder.build()
  }

  override fun isSubtype(type: MungoType): Boolean {
    return true
  }

  override fun leastUpperBound(type: MungoType): MungoType {
    return type
  }

  override fun mostSpecific(type: MungoType): MungoType? {
    return this
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    return other is MungoBottomType
  }

  override fun hashCode(): Int {
    return 0
  }

  override fun toString(): String {
    return "MungoBottomType"
  }

}
