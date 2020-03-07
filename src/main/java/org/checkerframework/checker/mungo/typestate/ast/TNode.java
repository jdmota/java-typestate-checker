package org.checkerframework.checker.mungo.typestate.ast;

public abstract class TNode {

  public final Position pos;

  public TNode(Position pos) {
    this.pos = pos;
  }

}
