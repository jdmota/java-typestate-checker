package org.checkerframework.checker.mungo.typestate.graph.exceptions;

import org.checkerframework.checker.mungo.typestate.ast.TIdNode;

public class StateNotDefined extends TypestateError {

  public static final long serialVersionUID = 0L;

  public final TIdNode id;

  public StateNotDefined(TIdNode id) {
    this.id = id;
  }

  @Override
  public String getMessage() {
    return String.format("State %s was not defined (%s)", id.name, id.pos.toString());
  }

}
