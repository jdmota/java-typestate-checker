package org.checkerframework.checker.mungo.typestate.graph;

import org.checkerframework.checker.mungo.typestate.ast.TMethodNode;
import org.checkerframework.checker.mungo.typestate.ast.TStateNode;

public class State extends AbstractState<TStateNode, TMethodNode> {

  public State(TStateNode node) {
    super(node);
  }
}
