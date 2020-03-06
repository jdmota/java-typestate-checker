package org.checkerframework.checker.mungo.typestate.ast;

import java.util.Map;

public class TDecisionStateNode extends TNode {

  public final Map<String, Object /*String | TStateNode*/> decisions;

  public TDecisionStateNode(Map<String, Object> decisions) {
    this.decisions = decisions;
  }

}
