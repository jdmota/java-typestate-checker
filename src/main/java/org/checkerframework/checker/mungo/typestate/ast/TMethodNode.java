package org.checkerframework.checker.mungo.typestate.ast;

import java.util.List;

public class TMethodNode extends TNode {

  public final String returnType;
  public final String name;
  public final List<String> args;
  public final TNode /*TIdNode | TStateNode | TDecisionStateNode*/ destination;

  public TMethodNode(Position pos, String returnType, String name, List<String> args, TNode destination) {
    super(pos);
    this.returnType = returnType;
    this.name = name;
    this.args = args;
    this.destination = destination;
  }

}
