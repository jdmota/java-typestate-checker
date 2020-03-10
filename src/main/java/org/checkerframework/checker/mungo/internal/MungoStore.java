package org.checkerframework.checker.mungo.internal;

import org.checkerframework.framework.flow.CFAbstractStore;

public class MungoStore extends CFAbstractStore<MungoValue, MungoStore> {

  public MungoStore(MungoAnalysis analysis, boolean sequentialSemantics) {
    super(analysis, sequentialSemantics);
  }

  public MungoStore(MungoStore other) {
    super(other);
  }
}
