package org.checkerframework.checker.mungo.typestate.graph.exceptions

import org.checkerframework.checker.mungo.typestate.ast.TStateNode

class UnusedStates(private val unusedStates: List<TStateNode>) : TypestateError() {
  override val message: String
    get() = String.format("Unused states in %s: %s", unusedStates[0].pos.basename, unusedStates.map { it.name }.joinToString("; "))

  companion object {
    const val serialVersionUID = 0L
  }
}
