package org.checkerframework.checker.mungo.typestate.graph.exceptions

abstract class TypestateError : RuntimeException() {
  companion object {
    const val serialVersionUID = 0L
  }
}
