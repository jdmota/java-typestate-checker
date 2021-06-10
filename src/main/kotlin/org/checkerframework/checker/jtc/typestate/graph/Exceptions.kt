package org.checkerframework.checker.jtc.typestate.graph

import org.checkerframework.checker.jtc.typestate.TIdNode
import org.checkerframework.checker.jtc.typestate.TStateNode

sealed class TypestateError : RuntimeException()

class DuplicateState(val first: TStateNode, val second: TStateNode) : TypestateError() {
  override val message: String
    get() = String.format("Duplicate state %s in %s at %s and %s", first.name, first.pos.basename, first.pos.lineCol, second.pos.lineCol)
}

class EnvCreationError : TypestateError() {
  override val message: String
    get() = "Failed to produce an environment in which to resolve the types in the typestate. Check if imports are correct."
}

class ReservedStateName(val state: TStateNode) : TypestateError() {
  override val message: String
    get() = String.format("%s is a reserved state name (%s)", state.name, state.pos.toString())
}

class StateNotDefined(val id: TIdNode) : TypestateError() {
  override val message: String
    get() = String.format("State %s was not defined (%s)", id.name, id.pos.toString())
}
