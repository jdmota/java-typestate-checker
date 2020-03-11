package org.checkerframework.checker.mungo.typestate.graph.exceptions

import org.checkerframework.checker.mungo.typestate.ast.TStateNode

class ReservedStateName(val state: TStateNode) : TypestateError() {
  override val message: String
    get() = String.format("%s is a reserved state name (%s)", state.name, state.pos.toString())

  companion object {
    const val serialVersionUID = 0L
  }
}
