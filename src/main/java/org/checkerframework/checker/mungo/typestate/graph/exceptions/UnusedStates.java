package org.checkerframework.checker.mungo.typestate.graph.exceptions;

import org.checkerframework.checker.mungo.typestate.ast.TStateNode;

import java.util.List;

public class UnusedStates extends TypestateError {

  public static final long serialVersionUID = 0L;

  private final List<TStateNode> unusedStates;

  public UnusedStates(List<TStateNode> unusedStates) {
    this.unusedStates = unusedStates;
  }

}
