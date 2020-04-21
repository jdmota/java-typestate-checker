package org.checkerframework.checker.mungo.typestate.graph.exceptions

class EnvCreationError : TypestateError() {
  override val message: String
    get() = "Failed to produce an environment in which to resolve the types in the typestate. Check if imports are correct."

  companion object {
    const val serialVersionUID = 0L
  }
}
