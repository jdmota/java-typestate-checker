package org.checkerframework.checker.mungo.analysis

import org.checkerframework.checker.mungo.typecheck.MungoNoProtocolType
import org.checkerframework.checker.mungo.typecheck.MungoUnknownType
import org.checkerframework.dataflow.analysis.FlowExpressions
import org.checkerframework.dataflow.cfg.node.FieldAccessNode
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode
import org.checkerframework.framework.flow.CFAbstractStore
import org.checkerframework.framework.type.AnnotatedTypeFactory
import javax.lang.model.element.ElementKind
import javax.lang.model.element.ExecutableElement

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

  override fun isSideEffectFree(atypeFactory: AnnotatedTypeFactory, method: ExecutableElement): Boolean {
    if (method.kind == ElementKind.CONSTRUCTOR && method.simpleName.toString() == "<init>") {
      // java.lang.Object constructor is side effect free
      return true
    }
    return super.isSideEffectFree(atypeFactory, method)
  }

  override fun updateForMethodCall(n: MethodInvocationNode, atypeFactory: AnnotatedTypeFactory, value: MungoValue?) {
    val oldFields = fieldValues
    val receiver = FlowExpressions.internalReprOf(atypeFactory, n.target.receiver)
    val receiverValue = getValue(receiver)

    // Call super method
    super.updateForMethodCall(n, atypeFactory, value)

    // See if the receiver is an object with protocol
    // In that case, we are controlling it, no need to invalidate it
    if (receiver is FlowExpressions.FieldAccess && receiverValue != null && !MungoNoProtocolType.SINGLETON.isSubtype(receiverValue.info)) {
      fieldValues[receiver] = receiverValue
    }

    // Do not remove entries for other fields
    // Since non-existent information is assumed to be the bottom type
    // Which is different from what Checker normally does (see description above)
    // See assign to unknown type
    for ((key, prevValue) in oldFields) {
      if (!fieldValues.containsKey(key)) {
        fieldValues[key] = MungoValue(prevValue, MungoUnknownType.SINGLETON)
      }
    }
  }

  fun leastUpperBoundFields(other: MungoStore, shouldWiden: Boolean = false): MungoStore {
    val newStore = analysis.createEmptyStore(sequentialSemantics)
    newStore.fieldValues = HashMap<FlowExpressions.FieldAccess, MungoValue>(fieldValues)
    newStore.thisValue = upperBoundOfValues(other.thisValue, thisValue, shouldWiden)
    for ((el, otherVal) in other.fieldValues.entries) {
      val merged = upperBoundOfValues(otherVal, fieldValues[el], shouldWiden)
      if (merged == null) newStore.fieldValues.remove(el) else newStore.fieldValues[el] = merged
    }
    return newStore
  }

  fun iterateOverLocalVars(): Iterator<Map.Entry<FlowExpressions.LocalVariable, MungoValue>> {
    return localVariableValues.iterator()
  }

  fun iterateOverFields(): Iterator<Map.Entry<FlowExpressions.FieldAccess, MungoValue>> {
    return fieldValues.iterator()
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
