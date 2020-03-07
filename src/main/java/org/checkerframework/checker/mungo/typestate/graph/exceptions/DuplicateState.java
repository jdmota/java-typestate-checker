package org.checkerframework.checker.mungo.typestate.graph.exceptions;

import org.checkerframework.checker.mungo.typestate.ast.TStateNode;

public class DuplicateState extends TypestateError {

  public static final long serialVersionUID = 0L;

  public final TStateNode first, second;

  public DuplicateState(TStateNode first, TStateNode second) {
    this.first = first;
    this.second = second;
  }

  @Override
  public String getMessage() {
    return String.format("Duplicate state %s in %s at %s and %s", first.name, first.pos.getBasename(), first.pos.getLineCol(), second.pos.getLineCol());
  }
}
