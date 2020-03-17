package org.checkerframework.checker.mungo.typecheck

import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.checker.mungo.typestate.graph.states.State

// Type information contains a set of possible states
// And the graph where those states belong
class MungoTypeInfo(val graph: Graph, val states: Set<State>) {

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other !is MungoTypeInfo) return false
    return graph == other.graph && states == other.states
  }

  // Probably won't need this... Just in case.
  override fun hashCode(): Int {
    var result = graph.hashCode()
    result = 31 * result + states.size // Faster than states.hashCode()
    return result
  }

  override fun toString(): String {
    return "MungoTypeInfo$states";
  }

}
