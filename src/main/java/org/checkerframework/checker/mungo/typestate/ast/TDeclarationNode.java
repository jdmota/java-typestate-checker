package org.checkerframework.checker.mungo.typestate.ast;

import java.util.List;

public class TDeclarationNode extends TNode {

  public final String name;
  public final List<TStateNode> states;

  public TDeclarationNode(Position pos, String name, List<TStateNode> states) {
    super(pos);
    this.name = name;
    this.states = states;
  }

}
