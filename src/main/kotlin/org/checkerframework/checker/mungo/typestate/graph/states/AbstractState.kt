package org.checkerframework.checker.mungo.typestate.graph.states

import org.checkerframework.checker.mungo.typestate.ast.TNode
import java.util.*

// TODO check duplicate transitions and stuff...

abstract class AbstractState<N : TNode, T : TNode>(var node: N?) {
  val transitions: MutableMap<T, AbstractState<*, *>>

  open fun addTransition(transition: T, destination: AbstractState<*, *>) {
    transitions[transition] = destination
  }

  init {
    transitions = HashMap()
  }
}
