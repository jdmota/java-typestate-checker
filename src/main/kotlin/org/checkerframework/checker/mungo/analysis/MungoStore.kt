package org.checkerframework.checker.mungo.analysis

import org.checkerframework.framework.flow.CFAbstractStore

class MungoStore : CFAbstractStore<MungoValue, MungoStore> {
  constructor(analysis: MungoAnalysis, sequentialSemantics: Boolean) : super(analysis, sequentialSemantics) {}
  constructor(other: MungoStore) : super(other) {}
}
