package org.checkerframework.checker.mungo.typestate.graph.exceptions

import org.checkerframework.checker.mungo.typestate.ast.TIdNode

class StateNotDefined(val id: TIdNode) : TypestateError() {
  override val message: String
    get() = String.format("State %s was not defined (%s)", id.name, id.pos.toString())

  companion object {
    const val serialVersionUID = 0L
  }
}
