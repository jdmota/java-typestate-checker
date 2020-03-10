package org.checkerframework.checker.mungo.typestate.graph.states;

import org.checkerframework.checker.mungo.typestate.ast.TMethodNode;
import org.checkerframework.checker.mungo.typestate.ast.TStateNode;
import org.checkerframework.checker.mungo.typestate.graph.states.AbstractState;
import org.checkerframework.checker.nullness.qual.Nullable;

public class State extends AbstractState<TStateNode, TMethodNode> {

  public String name;

  protected State(String name) {
    super(null);
    this.name = name;
  }

  public State(@Nullable TStateNode node) {
    super(node);
    this.name = node == null ? "unknown" : node.name;
  }

  @Override
  public String toString() {
    return "State{name=" + name + ",node=" + node + "}";
  }
}
