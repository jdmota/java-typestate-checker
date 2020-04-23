package org.checkerframework.checker.mungo.analysis

import org.checkerframework.checker.mungo.typecheck.MungoNoProtocolType
import org.checkerframework.checker.mungo.typecheck.MungoTypecheck
import org.checkerframework.checker.mungo.typecheck.MungoUnknownType
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.dataflow.analysis.FlowExpressions
import org.checkerframework.dataflow.cfg.node.*
import org.checkerframework.framework.flow.CFAbstractStore
import org.checkerframework.framework.type.AnnotatedTypeFactory
import org.checkerframework.javacutil.Pair
import javax.lang.model.element.ElementKind
import javax.lang.model.element.ExecutableElement
import javax.lang.model.element.VariableElement
import javax.lang.model.type.TypeMirror

class MungoStore : CFAbstractStore<MungoValue, MungoStore> {

  private val a: MungoAnalysis

  constructor(analysis: MungoAnalysis, sequentialSemantics: Boolean) : super(analysis, sequentialSemantics) {
    a = analysis
  }

  constructor(other: MungoStore) : super(other) {
    a = other.a
  }

  private val utils get() = a.c.utils

  // We adapt the default implementation of CFAbstractStore#leastUpperBound.
  // Issue: the exit store of a method should include all variables so they can be checked.

  // Description:
  // Analysis#mergeStores does not call "leastUpperBound" and immediately returns one store if the other is null.
  // Shouldn't a "null" store be equivalent to an empty one?
  // Unfortunately, if "other" is an empty store, the end result is an empty store, which loses information.
  // We believe the least upper bound of two stores should be union of the two.
  // We consider that if a variable is not present, it is as if it had the bottom type,
  // since trying to use an unreferenced variable would produce an error.

  // Note 1: we keep "bottom" entries so that when Checker reads the store, does not see "null" and defaults to the annotated type

  // Note 2: in a comment inside CFAbstractStore#upperBound, the authors argue that variables present
  // in one store and not in the other have implicitly the "top" type.
  // Which is fine, since everything belongs to the "top" type.
  // But we believe we can be more specific, and avoid losing useful information.

  // Side effects: information about variables declared inside loops, is preserved for the next loop.
  // Should be fine since the declaration will override previous information.

  // TODO we have to make sure this decision is safe and consistent everywhere

  override fun leastUpperBound(other: MungoStore): MungoStore {
    return upperBound(other, false)
  }

  override fun widenedUpperBound(previous: MungoStore): MungoStore {
    return upperBound(previous, true)
  }

  // Adapted from CFAbstractStore#upperBound
  private fun upperBound(other: MungoStore, shouldWiden: Boolean): MungoStore {
    val newStore = analysis.createCopiedStore(this)
    if (thisValue != null || other.thisValue != null) {
      newStore.thisValue = upperBoundOfValues(other.thisValue, thisValue, shouldWiden)
    } else {
      newStore.thisValue = null
    }
    for ((el, otherVal) in other.localVariableValues.entries) {
      newStore.localVariableValues[el] = upperBoundOfValues(otherVal, localVariableValues[el], shouldWiden)
    }
    for ((el, otherVal) in other.fieldValues.entries) {
      newStore.fieldValues[el] = upperBoundOfValues(otherVal, fieldValues[el], shouldWiden)
    }
    for ((el, otherVal) in other.arrayValues.entries) {
      newStore.arrayValues[el] = upperBoundOfValues(otherVal, arrayValues[el], shouldWiden)
    }
    for ((el, otherVal) in other.methodValues.entries) {
      newStore.methodValues[el] = upperBoundOfValues(otherVal, methodValues[el], shouldWiden)
    }
    for ((el, otherVal) in other.classValues.entries) {
      newStore.classValues[el] = upperBoundOfValues(otherVal, classValues[el], shouldWiden)
    }
    return newStore
  }

  // Adapted from CFAbstract#upperBoundOfValues
  private fun upperBoundOfValues(a: MungoValue?, b: MungoValue?, shouldWiden: Boolean): MungoValue {
    if (a == null) return b!!
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

  // TODO infer method side-effects so that we do not just invalidate everything upon a method call...

  override fun updateForMethodCall(n: MethodInvocationNode, atypeFactory: AnnotatedTypeFactory, value: MungoValue?) {
    val oldFields = fieldValues
    val receiver = FlowExpressions.internalReprOf(atypeFactory, n.target.receiver)
    val receiverValue = getValue(receiver)

    // Call super method
    super.updateForMethodCall(n, atypeFactory, value)

    // See if the current class has protocol and if the receiver is an object with protocol
    // In that case, we are controlling it, no need to invalidate it
    if (a.inClassAnalysis) {
      if (receiver is FlowExpressions.FieldAccess && !MungoNoProtocolType.SINGLETON.isSubtype(receiverValue.info)) {
        fieldValues[receiver] = receiverValue
      }
    }

    // Since non-existent information is assumed to be the bottom type, do not remove entries for other fields
    // Which is different from what Checker normally does (see description above)
    for ((key, prevValue) in oldFields) {
      if (!fieldValues.containsKey(key)) {
        fieldValues[key] = MungoValue(prevValue, MungoTypecheck.invalidate(utils, key.type))
      }
    }
  }

  fun leastUpperBoundFields(other: MungoStore, shouldWiden: Boolean = false): MungoStore {
    val newStore = analysis.createEmptyStore(sequentialSemantics)
    newStore.fieldValues = HashMap(fieldValues)
    for ((el, otherVal) in other.fieldValues.entries) {
      newStore.fieldValues[el] = upperBoundOfValues(otherVal, fieldValues[el], shouldWiden)
    }
    return newStore
  }

  fun toBottom(): MungoStore {
    val newStore = analysis.createEmptyStore(sequentialSemantics)
    newStore.thisValue = thisValue?.toBottom()
    for ((el, value) in localVariableValues.entries) {
      newStore.localVariableValues[el] = value.toBottom()
    }
    for ((el, value) in fieldValues.entries) {
      newStore.fieldValues[el] = value.toBottom()
    }
    for ((el, value) in arrayValues.entries) {
      newStore.arrayValues[el] = value.toBottom()
    }
    for ((el, value) in methodValues.entries) {
      newStore.methodValues[el] = value.toBottom()
    }
    for ((el, value) in classValues.entries) {
      newStore.classValues[el] = value.toBottom()
    }
    return newStore
  }

  fun iterateOverLocalVars(): Iterator<Map.Entry<FlowExpressions.LocalVariable, MungoValue>> {
    return localVariableValues.iterator()
  }

  fun iterateOverFields(): Iterator<Map.Entry<FlowExpressions.FieldAccess, MungoValue>> {
    return fieldValues.iterator()
  }

  fun getFields(): List<Pair<VariableElement, MungoValue>> {
    return fieldValues.map { (key, value) -> Pair.of(key.field, value) }
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
    val value = MungoValue(old, valueToMerge.info.intersect(old.info))
    return if (value != old) {
      super.replaceValue(r, value)
      true
    } else {
      false
    }
  }

  override fun insertValue(r: FlowExpressions.Receiver, value: MungoValue?) {
    if (a.inClassAnalysis && a.creatingInitialStore && r is FlowExpressions.FieldAccess) {
      // Workaround CFTransfer#initialStore modifying information of our fixed store
      return
    }
    super.insertValue(r, value)
  }

  private fun getUnknownValue(type: TypeMirror) = MungoValue(a, MungoTypecheck.invalidate(utils, type), type)

  override fun getValue(expr: FlowExpressions.Receiver): MungoValue {
    // Workaround
    val value = if (expr is FlowExpressions.Unknown) null else super.getValue(expr)
    // Make sure we do not return null so that Checker does not default to the annotated type.
    // Note: even though we assume a non existent entry has the bottom type, we return the unknown type
    // to not let potential issues going unnoticed.
    return value ?: getUnknownValue(expr.type)
  }

  override fun getValue(n: ArrayAccessNode): MungoValue {
    return super.getValue(n) ?: getUnknownValue(n.type)
  }

  override fun getValue(n: FieldAccessNode): MungoValue {
    return super.getValue(n) ?: getUnknownValue(n.type)
  }

  fun getValueIfTracked(n: LocalVariableNode) = super.getValue(n)

  override fun getValue(n: LocalVariableNode): MungoValue {
    return super.getValue(n) ?: getUnknownValue(n.type)
  }

  override fun getValue(n: MethodInvocationNode): MungoValue {
    return super.getValue(n) ?: getUnknownValue(n.type)
  }

  override fun getValue(n: ThisLiteralNode): MungoValue {
    return super.getValue(n) ?: getUnknownValue(n.type)
  }
}
