package org.checkerframework.checker.mungo.typestate.ast;

import java.util.List;

public class TDeclarationNode extends TNode {

  public final String name;
  public final List<TStateNode> states;

  public TDeclarationNode(String name, List<TStateNode> states) {
    this.name = name;
    this.states = states;
  }

}
