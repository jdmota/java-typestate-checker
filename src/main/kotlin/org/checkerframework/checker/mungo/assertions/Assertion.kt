package org.checkerframework.checker.mungo.assertions

import org.checkerframework.checker.mungo.analysis.Reference
import org.checkerframework.checker.mungo.typecheck.MungoType

class AccessLocation(val ref: Reference, val isZero: Boolean) {
  override fun equals(other: Any?): Boolean {
    if (other !is AccessLocation) return false
    return other.ref == ref && other.isZero == isZero
  }

  override fun hashCode(): Int {
    var result = ref.hashCode()
    result = 31 * result + isZero.hashCode()
    return result
  }

  override fun toString(): String {
    return if (isZero) "$ref.0" else "$ref"
  }
}

class Assertion {

  val accesses = mutableMapOf<AccessLocation, Fraction>()
  val typeofs = mutableMapOf<Reference, MungoType>()
  val packed = mutableMapOf<Reference, Boolean>()
  val equalities = MutableEqualityTracker()

}
