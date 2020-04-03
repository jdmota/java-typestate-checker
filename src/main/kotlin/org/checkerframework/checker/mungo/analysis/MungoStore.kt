package org.checkerframework.checker.mungo.analysis

import org.checkerframework.dataflow.analysis.FlowExpressions
import org.checkerframework.framework.flow.CFAbstractStore

class MungoStore : CFAbstractStore<MungoValue, MungoStore> {
  constructor(analysis: MungoAnalysis, sequentialSemantics: Boolean) : super(analysis, sequentialSemantics)
  constructor(other: MungoStore) : super(other)

  // We adapt the default implementation of CFAbstractStore#leastUpperBound.
  // Issue: the exit store of a method should include all variables so they can be checked.

  // Description:
  // Analysis#mergeStores does not call "leastUpperBound" and immediately returns one store if the other is null.
  // Shouldn't a "null" store be equivalent to an empty one?
  // Unfortunately, if "other" is an empty store, the end result is an empty store, which loses information.
  // We believe the least upper bound of two stores should be union of the two.
  // We consider that if a variable is not present, it is as if it had the bottom type,
  // since trying to use an unreferenced variable would produce an error.

  // Note: in a comment inside CFAbstractStore#upperBound, the authors argue that variables present
  // in one store and not in the other have implicitly the "top" type.
  // Which is fine, since everything belongs to the "top" type.
  // But we believe we can be more specific, and avoid losing useful information.

  // Side effects: information about variables declared inside loops, is preserved for the next loop.
  // Should be fine since the declaration will override previous information.

  // TODO report?

  override fun leastUpperBound(other: MungoStore): MungoStore {
    return upperBound(other, false)
  }

  override fun widenedUpperBound(previous: MungoStore): MungoStore {
    return upperBound(previous, true)
  }

  // Adapted from CFAbstractStore#upperBound
  private fun upperBound(other: MungoStore, shouldWiden: Boolean): MungoStore {
    val newStore = analysis.createCopiedStore(this)
    newStore.thisValue = upperBoundOfValues(other.thisValue, thisValue, shouldWiden)
    for ((el, otherVal) in other.localVariableValues.entries) {
      val merged = upperBoundOfValues(otherVal, localVariableValues[el], shouldWiden)
      if (merged == null) newStore.localVariableValues.remove(el) else newStore.localVariableValues[el] = merged
    }
    for ((el, otherVal) in other.fieldValues.entries) {
      val merged = upperBoundOfValues(otherVal, fieldValues[el], shouldWiden)
      if (merged == null) newStore.fieldValues.remove(el) else newStore.fieldValues[el] = merged
    }
    for ((el, otherVal) in other.arrayValues.entries) {
      val merged = upperBoundOfValues(otherVal, arrayValues[el], shouldWiden)
      if (merged == null) newStore.arrayValues.remove(el) else newStore.arrayValues[el] = merged
    }
    for ((el, otherVal) in other.methodValues.entries) {
      val merged = upperBoundOfValues(otherVal, methodValues[el], shouldWiden)
      if (merged == null) newStore.methodValues.remove(el) else newStore.methodValues[el] = merged
    }
    for ((el, otherVal) in other.classValues.entries) {
      val merged = upperBoundOfValues(otherVal, classValues[el], shouldWiden)
      if (merged == null) newStore.classValues.remove(el) else newStore.classValues[el] = merged
    }
    return newStore
  }

  // Adapted from CFAbstract#upperBoundOfValues
  private fun upperBoundOfValues(a: MungoValue?, b: MungoValue?, shouldWiden: Boolean): MungoValue? {
    if (a == null) return b
    if (b == null) return a
    return if (shouldWiden) b.widenUpperBound(a) else b.leastUpperBound(a)
  }

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
