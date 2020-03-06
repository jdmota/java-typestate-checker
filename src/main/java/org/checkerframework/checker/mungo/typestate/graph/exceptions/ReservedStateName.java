package org.checkerframework.checker.mungo.typestate.graph.exceptions;

import org.checkerframework.checker.mungo.typestate.ast.TStateNode;

public class ReservedStateName extends TypestateError {

  public static final long serialVersionUID = 0L;

  public final TStateNode state;

  public ReservedStateName(TStateNode state) {
    this.state = state;
  }

}
