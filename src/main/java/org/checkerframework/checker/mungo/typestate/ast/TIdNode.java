package org.checkerframework.checker.mungo.typestate.ast;

public class TIdNode extends TNode {

  public final String name;

  public TIdNode(Position pos, String name) {
    super(pos);
    this.name = name;
  }

}
