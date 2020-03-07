package org.checkerframework.checker.mungo.typestate.ast;

import java.util.List;

public class TStateNode extends TNode {

  public final String /*or null*/ name;
  public final List<TMethodNode> methods;

  public TStateNode(Position pos, String name, List<TMethodNode> methods) {
    super(pos);
    this.name = name;
    this.methods = methods;
  }

}
