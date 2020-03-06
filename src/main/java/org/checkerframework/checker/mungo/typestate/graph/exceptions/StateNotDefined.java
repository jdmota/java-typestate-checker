package org.checkerframework.checker.mungo.typestate.graph.exceptions;

public class StateNotDefined extends TypestateError {

  public static final long serialVersionUID = 0L;

  public final String stateName;
  // TODO location

  public StateNotDefined(String stateName) {
    this.stateName = stateName;
  }

}
