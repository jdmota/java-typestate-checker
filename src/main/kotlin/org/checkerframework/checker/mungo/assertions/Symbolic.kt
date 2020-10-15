package org.checkerframework.checker.mungo.assertions

import org.checkerframework.checker.mungo.analysis.Reference
import org.checkerframework.checker.mungo.typecheck.MungoType
import org.checkerframework.checker.mungo.typecheck.MungoUnionType
import org.checkerframework.checker.mungo.typecheck.MungoUnknownType

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

abstract class Cloneable<T> {
  abstract fun clone(): T
}

fun <K, V : Cloneable<V>> clone(map: Map<K, V>): MutableMap<K, V> {
  val newMap = mutableMapOf<K, V>()
  for ((key, value) in map) {
    newMap[key] = value.clone()
  }
  return newMap
}

enum class Bool3 {
  YES {
    override fun negate() = NO
  },
  NO {
    override fun negate() = YES
  },
  UNKNOWN {
    override fun negate() = UNKNOWN
  };

  abstract fun negate(): Bool3
}

class SymbolicFraction(
  private var isZero: Bool3 = Bool3.UNKNOWN,
  private var isOne: Bool3 = Bool3.UNKNOWN
) : Cloneable<SymbolicFraction>() {
  fun zero(): SymbolicFraction {
    isZero = Bool3.YES
    isOne = Bool3.NO
    return this
  }

  fun one(): SymbolicFraction {
    isZero = Bool3.NO
    isOne = Bool3.YES
    return this
  }

  fun read(): SymbolicFraction {
    isZero = Bool3.NO
    isOne = Bool3.UNKNOWN
    return this
  }

  override fun clone() = SymbolicFraction(isZero, isOne)
}

class SymbolicType(
  private var subtypeOf: MungoType = MungoUnknownType.SINGLETON
) : Cloneable<SymbolicType>() {
  fun subtype(type: MungoType) {
    subtypeOf = MungoUnionType.join(type, subtypeOf)
  }

  override fun clone() = SymbolicType(subtypeOf)
}

class SymbolicAssertion(
  private val accesses: MutableMap<AccessLocation, SymbolicFraction> = mutableMapOf(),
  private val typeofs: MutableMap<Reference, SymbolicType> = mutableMapOf(),
  //private val packed: MutableMap<Reference, Boolean> = mutableMapOf(),
  private val equalities: MutableEqualityTracker = MutableEqualityTracker()
) {

  constructor(locations: Collection<Reference>) : this() {
    for (loc in locations) {
      accesses[AccessLocation(loc, false)] = SymbolicFraction()
      typeofs[loc] = SymbolicType()
    }
  }

  fun addAccess(loc: AccessLocation, fraction: SymbolicFraction) {
    accesses[loc] = fraction
  }

  fun addTypeof(loc: Reference, type: SymbolicType) {
    typeofs[loc] = type
  }

  /*fun addPacked(loc: Reference, bool: Boolean) {
    packed[loc] = bool
  }*/

  fun addEq(x: Reference, y: Reference) {
    equalities.setEquality(x, y)
  }

  fun getAccess(loc: AccessLocation) = accesses[loc]

  fun getTypeof(loc: Reference) = typeofs[loc]

  //fun getPacked(loc: Reference) = packed[loc]

  fun getEq(x: Reference, y: Reference) {
    equalities.setEquality(x, y)
  }

  fun clone(): SymbolicAssertion {
    return SymbolicAssertion(
      clone(accesses),
      clone(typeofs),
      //clone(packed),
      equalities.clone()
    )
  }

  companion object {
    fun implies(a: SymbolicAssertion, b: SymbolicAssertion) {

    }
  }

}
