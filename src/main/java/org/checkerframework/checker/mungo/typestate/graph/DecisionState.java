package org.checkerframework.checker.mungo.typestate.graph;

import org.checkerframework.checker.mungo.typestate.ast.TDecisionNode;
import org.checkerframework.checker.mungo.typestate.ast.TDecisionStateNode;

public class DecisionState extends AbstractState<TDecisionStateNode, TDecisionNode> {

  public DecisionState(TDecisionStateNode node) {
    super(node);
  }

  @Override
  public String toString() {
    return "DecisionState{node=" + node + "}";
  }
}
