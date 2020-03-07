package org.checkerframework.checker.mungo.typestate.graph.states;

import org.checkerframework.checker.mungo.typestate.ast.TDecisionNode;
import org.checkerframework.checker.mungo.typestate.ast.TDecisionStateNode;
import org.checkerframework.checker.mungo.typestate.graph.states.AbstractState;

public class DecisionState extends AbstractState<TDecisionStateNode, TDecisionNode> {

  public DecisionState(TDecisionStateNode node) {
    super(node);
  }

  @Override
  public String toString() {
    return "DecisionState{node=" + node + "}";
  }
}
