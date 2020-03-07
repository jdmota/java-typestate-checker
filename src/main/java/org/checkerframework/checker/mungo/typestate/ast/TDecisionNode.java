package org.checkerframework.checker.mungo.typestate.ast;

public class TDecisionNode extends TNode {

  public final String label;
  public final TNode /*TIdNode | TStateNode*/ destination;

  public TDecisionNode(Position pos, String label, TNode destination) {
    super(pos);
    this.label = label;
    this.destination = destination;
  }

}
