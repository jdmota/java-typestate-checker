package org.checkerframework.checker.mungo.typecheck

import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.checker.mungo.typestate.graph.states.State

sealed class MungoType

// Type information contains a set of possible states
// And the graph where those states belong
class MungoConcreteType(val graph: Graph, val states: Set<State>) : MungoType() {

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

class MungoNullType : MungoType() {

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

class MungoUnknownType : MungoType() {

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

class MungoBottomType : MungoType() {

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
