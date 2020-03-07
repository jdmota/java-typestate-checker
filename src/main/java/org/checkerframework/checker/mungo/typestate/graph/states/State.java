package org.checkerframework.checker.mungo.typestate.graph.states;

import org.checkerframework.checker.mungo.typestate.ast.TMethodNode;
import org.checkerframework.checker.mungo.typestate.ast.TStateNode;
import org.checkerframework.checker.mungo.typestate.graph.states.AbstractState;

public class State extends AbstractState<TStateNode, TMethodNode> {

  public State(TStateNode node) {
    super(node);
  }

  @Override
  public String toString() {
    return "State{name=" + (node == null ? "unknown" : node.name) + ",node=" + node + "}";
  }
}
