package org.checkerframework.checker.mungo.typestate.ast;

import java.util.List;

public class TDecisionStateNode extends TNode {

  public final List<TDecisionNode> decisions;

  public TDecisionStateNode(List<TDecisionNode> decisions) {
    this.decisions = decisions;
  }

}
