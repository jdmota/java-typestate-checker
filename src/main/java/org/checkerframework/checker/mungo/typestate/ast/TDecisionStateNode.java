package org.checkerframework.checker.mungo.typestate.ast;

import java.util.List;

public class TDecisionStateNode extends TNode {

  public final List<TDecisionNode> decisions;

  public TDecisionStateNode(Position pos, List<TDecisionNode> decisions) {
    super(pos);
    this.decisions = decisions;
  }

}
