package org.checkerframework.checker.mungo.typestate.graph.exceptions

import org.checkerframework.checker.mungo.typestate.ast.TStateNode
import java.util.stream.Collectors

class UnusedStates(private val unusedStates: List<TStateNode>) : TypestateError() {
  override val message: String
    get() = String.format("Unused states in %s: %s", unusedStates[0].pos.basename, unusedStates.stream().map { it.name }.collect(Collectors.joining("; ")))

  companion object {
    const val serialVersionUID = 0L
  }
}
