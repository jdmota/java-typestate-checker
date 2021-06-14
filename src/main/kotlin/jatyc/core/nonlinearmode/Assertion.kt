package jatyc.core.nonlinearmode

import jatyc.core.*

// This implementation is inspired in concepts present in https://github.com/immutable-js/immutable-js

internal class UniqOwner

class AssertionNode internal constructor(
  internal var fraction: Fraction,
  internal var packedFraction: Fraction,
  internal var type: JTCType,
  internal var children: MutableMap<ReverseRefComponent, AssertionNode>?,
  internal val owner: UniqOwner?
) {
  companion object {
    val DEFAULT = AssertionNode(Fraction.ZERO, Fraction.ZERO, JTCUnknownType.SINGLETON, null, null)

    internal fun new(owner: UniqOwner?): AssertionNode {
      if (owner == null) return DEFAULT
      return AssertionNode(Fraction.ZERO, Fraction.ZERO, JTCUnknownType.SINGLETON, null, owner)
    }
  }

  private fun update(owner: UniqOwner?, fn: (AssertionNode) -> Unit): AssertionNode {
    val isEditable = owner != null && this.owner == owner
    val toEdit = if (isEditable) this else clone(owner)
    fn(toEdit)
    return toEdit
  }

  internal fun update(ref: ReverseRef, owner: UniqOwner?, fn: (AssertionNode) -> Unit): AssertionNode {
    val isEditable = owner != null && this.owner == owner

    val children = if (isEditable) children ?: mutableMapOf() else children?.toMutableMap() ?: mutableMapOf()

    val info = children.computeIfAbsent(ref.id) { new(owner) }
    children[ref.id] = if (ref.rest == null) info.update(owner, fn) else info.update(ref.rest, owner, fn)

    return if (isEditable) this else AssertionNode(fraction, packedFraction, type, children, owner)
  }

  private fun clone(owner: UniqOwner?): AssertionNode {
    return AssertionNode(fraction, packedFraction, type, children, owner)
  }
}

class Assertion internal constructor(private var root: AssertionNode, private val owner: UniqOwner?) {
  companion object {
    val EMPTY = Assertion(AssertionNode.DEFAULT, null)
  }

  // TODO create getters

  // TODO how to manipulate from outside?
  fun update(ref: Reference, fn: (AssertionNode) -> Unit): Assertion {
    val isEditable = owner != null
    val newRoot = root.update(ReverseRef.make(ref), owner, fn)
    return if (isEditable) {
      root = newRoot
      this
    } else Assertion(newRoot, null)
  }

  // This method is suited for multiple updates at once
  fun update(fn: (Assertion) -> Unit): Assertion {
    val isEditable = owner != null
    return if (isEditable) {
      fn(this)
      this
    } else {
      val assertion = Assertion(root, UniqOwner()) // Create mutable assertion
      fn(assertion)
      Assertion(assertion.root, null) // Return an immutable assertion
    }
  }
}
