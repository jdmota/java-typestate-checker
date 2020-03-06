package org.checkerframework.checker.mungo.typestate.graph;

import org.checkerframework.checker.mungo.typestate.ast.TMethodNode;
import org.checkerframework.checker.mungo.typestate.ast.TStateNode;

public class EndState extends State {

  public EndState(TStateNode node) {
    super(node);
  }

  @Override
  public void addTransition(TMethodNode transition, AbstractState<?, ?> destination) {
    throw new AssertionError("end state should have no transitions");
  }
}
