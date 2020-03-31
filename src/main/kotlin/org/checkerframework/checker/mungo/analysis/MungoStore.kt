package org.checkerframework.checker.mungo.analysis

import org.checkerframework.checker.mungo.typecheck.MungoBottomType
import org.checkerframework.dataflow.analysis.FlowExpressions
import org.checkerframework.framework.flow.CFAbstractStore

class MungoStore : CFAbstractStore<MungoValue, MungoStore> {
  constructor(analysis: MungoAnalysis, sequentialSemantics: Boolean) : super(analysis, sequentialSemantics)
  constructor(other: MungoStore) : super(other)

  fun iterateOverLocalVars(): Iterator<Map.Entry<FlowExpressions.LocalVariable, MungoValue>> {
    return localVariableValues.iterator()
  }

  fun replaceValueIfDiff(r: FlowExpressions.Receiver, value: MungoValue): Boolean {
    val old = this.getValue(r)
    return if (value != old) {
      super.replaceValue(r, value)
      true
    } else {
      false
    }
  }

  fun intersectValueIfDiff(r: FlowExpressions.Receiver, valueToMerge: MungoValue): Boolean {
    val old = this.getValue(r)
    val value = if (old == null) valueToMerge else MungoValue(old, valueToMerge.info.intersect(old.info))
    return if (value != old) {
      super.replaceValue(r, value)
      true
    } else {
      false
    }
  }
}
