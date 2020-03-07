package org.checkerframework.checker.mungo.typestate.graph.exceptions;

import org.checkerframework.checker.mungo.typestate.ast.TStateNode;

import java.util.List;
import java.util.stream.Collectors;

public class UnusedStates extends TypestateError {

  public static final long serialVersionUID = 0L;

  private final List<TStateNode> unusedStates;

  public UnusedStates(List<TStateNode> unusedStates) {
    this.unusedStates = unusedStates;
  }

  @Override
  public String getMessage() {
    return String.format("Unused states in %s: %s", unusedStates.get(0).pos.getBasename(), unusedStates.stream().map(s -> s.name).collect(Collectors.joining("; ")));
  }

}
