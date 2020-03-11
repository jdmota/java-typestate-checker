package org.checkerframework.checker.mungo.typestate.graph.states

import org.checkerframework.checker.mungo.typestate.ast.TMethodNode

class EndState : State("end") {
  override fun addTransition(transition: TMethodNode, destination: AbstractState<*, *>) {
    throw AssertionError("end state should have no transitions")
  }
}
