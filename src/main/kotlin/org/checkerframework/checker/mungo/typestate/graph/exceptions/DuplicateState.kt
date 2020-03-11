package org.checkerframework.checker.mungo.typestate.graph.exceptions

import org.checkerframework.checker.mungo.typestate.ast.TStateNode

class DuplicateState(val first: TStateNode, val second: TStateNode) : TypestateError() {
  override val message: String
    get() = String.format("Duplicate state %s in %s at %s and %s", first.name, first.pos.basename, first.pos.lineCol, second.pos.lineCol)

  companion object {
    const val serialVersionUID = 0L
  }
}
