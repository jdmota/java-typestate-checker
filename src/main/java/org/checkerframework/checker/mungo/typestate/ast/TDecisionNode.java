package org.checkerframework.checker.mungo.typestate.ast;

public class TDecisionNode extends TNode {

  public final String label;
  public final Object /*String | TStateNode*/ destination;

  public TDecisionNode(String label, Object destination) {
    this.label = label;
    this.destination = destination;
  }

}
