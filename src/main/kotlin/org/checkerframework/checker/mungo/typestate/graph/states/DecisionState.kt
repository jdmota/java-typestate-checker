package org.checkerframework.checker.mungo.typestate.graph.states

import org.checkerframework.checker.mungo.typestate.ast.TDecisionNode
import org.checkerframework.checker.mungo.typestate.ast.TDecisionStateNode
import java.util.HashMap

class DecisionState(node: TDecisionStateNode?) : AbstractState<TDecisionStateNode>(node) {

  val transitions: MutableMap<TDecisionNode, State> = HashMap()

  fun addTransition(transition: TDecisionNode, destination: State) {
    transitions[transition] = destination
  }

  override fun toString(): String {
    return "DecisionState{node=$node}"
  }
}
