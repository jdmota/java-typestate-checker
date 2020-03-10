package org.checkerframework.checker.mungo.typestate.graph.states;

import org.checkerframework.checker.mungo.typestate.ast.TNode;
import org.checkerframework.checker.nullness.qual.Nullable;

import java.util.HashMap;
import java.util.Map;

public abstract class AbstractState<N extends TNode, T extends TNode> {

  // TODO check duplicate transitions and stuff...

  public @Nullable N node;
  public Map<T, AbstractState<?, ?>> transitions;

  public AbstractState(@Nullable N node) {
    this.node = node;
    this.transitions = new HashMap<>();
  }

  public void addTransition(T transition, AbstractState<?, ?> destination) {
    transitions.put(transition, destination);
  }

}
