package org.checkerframework.checker.jtc.core.linearmode

import org.checkerframework.checker.jtc.core.JTCBottomType
import org.checkerframework.checker.jtc.core.JTCType
import org.checkerframework.checker.jtc.core.JTCUnknownType
import org.checkerframework.checker.jtc.core.Reference

sealed class StoreInfo(val type: JTCType) {
  abstract fun conditionalOn(ref: Reference): Boolean
  abstract fun replaceCondition(ref: Reference): StoreInfo
  abstract fun fixThis(from: Reference, to: Reference): StoreInfo
  abstract fun union(other: StoreInfo): StoreInfo
  abstract fun toRegular(): RegularStoreInfo
  abstract fun withLabel(ref: Reference, label: String?): RegularStoreInfo
  abstract fun withoutLabel(ref: Reference, label: String?): RegularStoreInfo
  abstract fun not(original: Reference, negation: Reference): StoreInfo

  companion object {
    val UNKNOWN = RegularStoreInfo(JTCUnknownType.SINGLETON)
    val BOTTOM = RegularStoreInfo(JTCBottomType.SINGLETON)
  }
}

class RegularStoreInfo(type: JTCType) : StoreInfo(type) {
  override fun conditionalOn(ref: Reference): Boolean {
    return false
  }

  override fun replaceCondition(ref: Reference): StoreInfo {
    return this
  }

  override fun fixThis(from: Reference, to: Reference): StoreInfo {
    return this
  }

  override fun union(other: StoreInfo): StoreInfo {
    return RegularStoreInfo(type.union(other.type))
  }

  override fun toRegular(): RegularStoreInfo {
    return this
  }

  override fun withLabel(ref: Reference, label: String?): RegularStoreInfo {
    return this
  }

  override fun withoutLabel(ref: Reference, label: String?): RegularStoreInfo {
    return this
  }

  override fun not(original: Reference, negation: Reference): StoreInfo {
    return this
  }

  override fun equals(other: Any?): Boolean {
    return other is RegularStoreInfo && type == other.type
  }

  override fun hashCode(): Int {
    return type.hashCode()
  }

  override fun toString(): String {
    return "Regular{${type.format()}}"
  }
}

class ConditionalStoreInfo(val condition: Reference, val thenType: JTCType, val elseType: JTCType) : StoreInfo(thenType.union(elseType)) {
  override fun conditionalOn(ref: Reference): Boolean {
    return condition == ref
  }

  override fun replaceCondition(ref: Reference): StoreInfo {
    return ConditionalStoreInfo(ref, thenType, elseType)
  }

  override fun fixThis(from: Reference, to: Reference): StoreInfo {
    return ConditionalStoreInfo(condition.fixThis(from, to), thenType, elseType)
  }

  override fun union(other: StoreInfo): StoreInfo {
    if (other is ConditionalStoreInfo && condition == other.condition) {
      return ConditionalStoreInfo(condition, thenType.union(other.thenType), elseType.union(other.elseType))
    }
    return RegularStoreInfo(type.union(other.type))
  }

  override fun toRegular(): RegularStoreInfo {
    return RegularStoreInfo(type)
  }

  override fun withLabel(ref: Reference, label: String?): RegularStoreInfo {
    return if (condition == ref) {
      RegularStoreInfo(when (label) {
        "true" -> thenType
        "false" -> elseType
        else -> type
      })
    } else {
      RegularStoreInfo(type)
    }
  }

  override fun withoutLabel(ref: Reference, label: String?): RegularStoreInfo {
    return if (condition == ref) {
      RegularStoreInfo(when (label) {
        "true" -> elseType
        "false" -> thenType
        else -> type
      })
    } else {
      RegularStoreInfo(type)
    }
  }

  override fun not(original: Reference, negation: Reference): StoreInfo {
    if (original == condition) {
      return ConditionalStoreInfo(negation, elseType, thenType)
    }
    return RegularStoreInfo(type)
  }

  override fun equals(other: Any?): Boolean {
    return other is ConditionalStoreInfo && condition == other.condition && thenType == other.thenType && elseType == other.elseType
  }

  override fun hashCode(): Int {
    var result = condition.hashCode()
    result = 31 * result + thenType.hashCode()
    result = 31 * result + elseType.hashCode()
    return result
  }

  override fun toString(): String {
    return "Conditional{cond=$condition, then=${thenType.format()}, else=${elseType.format()}}"
  }
}

class CasesStoreInfo(val testValue: Reference, val cases: Map<String, JTCType>) : StoreInfo(JTCType.createUnion(cases.values)) {
  override fun conditionalOn(ref: Reference): Boolean {
    return testValue == ref
  }

  override fun replaceCondition(ref: Reference): StoreInfo {
    return CasesStoreInfo(ref, cases)
  }

  override fun fixThis(from: Reference, to: Reference): StoreInfo {
    return CasesStoreInfo(testValue.fixThis(from, to), cases)
  }

  override fun union(other: StoreInfo): StoreInfo {
    // TODO improve?
    return RegularStoreInfo(type.union(other.type))
  }

  override fun toRegular(): RegularStoreInfo {
    return RegularStoreInfo(type)
  }

  override fun withLabel(ref: Reference, label: String?): RegularStoreInfo {
    return if (testValue == ref) {
      RegularStoreInfo(if (label == null) type else cases[label] ?: type)
    } else {
      RegularStoreInfo(type)
    }
  }

  override fun withoutLabel(ref: Reference, label: String?): RegularStoreInfo {
    return if (testValue == ref) {
      RegularStoreInfo(if (label == null) type else JTCType.createUnion(cases.filterKeys { it != label }.values))
    } else {
      RegularStoreInfo(type)
    }
  }

  override fun not(original: Reference, negation: Reference): StoreInfo {
    return RegularStoreInfo(type)
  }

  override fun equals(other: Any?): Boolean {
    return other is CasesStoreInfo && testValue == other.testValue && cases == other.cases
  }

  override fun hashCode(): Int {
    var result = testValue.hashCode()
    result = 31 * result + cases.hashCode()
    return result
  }

  override fun toString(): String {
    return "Cases{value=$testValue, cases=$cases}"
  }
}

class Store(private val map: MutableMap<Reference, StoreInfo> = mutableMapOf()) {

  operator fun contains(ref: Reference) = map.contains(ref)
  operator fun get(ref: Reference): StoreInfo = map[ref] ?: StoreInfo.UNKNOWN
  operator fun iterator(): Iterator<Map.Entry<Reference, StoreInfo>> = map.iterator()

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    return other is Store && map == other.map
  }

  override fun hashCode(): Int {
    return map.hashCode()
  }

  override fun toString(): String {
    return map.toString()
  }

  operator fun set(ref: Reference, info: StoreInfo) {
    map[ref] = info
  }

  operator fun set(ref: Reference, type: JTCType) {
    map[ref] = RegularStoreInfo(type)
  }

  fun merge(ref: Reference, info: StoreInfo): Boolean {
    val curr = map[ref]
    val next = curr?.union(info) ?: info
    map[ref] = next
    return curr != next
  }

  fun remove(ref: Reference): StoreInfo? {
    return map.remove(ref)
  }

  fun clone(): Store {
    return Store(map.toMutableMap())
  }

  fun toBottom() {
    for ((ref, _) in map) {
      map[ref] = StoreInfo.BOTTOM
    }
  }

  fun invalidateFieldsOf(thisRef: Reference) {
    for ((ref, _) in map) {
      if (ref.isFieldOf(thisRef)) {
        map[ref] = StoreInfo.UNKNOWN
      }
    }
  }

  fun withLabel(condition: Reference, label: String?): Store {
    val store = Store()
    for ((ref, info) in this) {
      store[ref] = info.withLabel(condition, label)
    }
    return store
  }

  fun toRegular(): Store {
    val store = Store()
    for ((ref, info) in this) {
      store[ref] = info.toRegular()
    }
    return store
  }

  fun toShared(): Store {
    val store = Store()
    for ((ref, info) in this) {
      store[ref] = info.type.toShared()
    }
    return store
  }

  fun propagateTo(other: Store): Boolean {
    var changed = false
    for ((ref, info) in this) {
      changed = other.merge(ref, info) || changed
    }
    return changed
  }

  fun fixThis(from: Reference, to: Reference): Store {
    val store = Store()
    for ((ref, info) in this) {
      store[ref.fixThis(from, to)] = info.fixThis(from, to)
    }
    return store
  }

  companion object {
    fun mergeToNew(a: Store, b: Store): Store {
      val store = a.clone()
      for ((ref, info) in b) {
        store.merge(ref, info)
      }
      return store
    }

    fun mergeFieldsToNew(a: Store, b: Store, thisRef: Reference): Store {
      val store = a.clone()
      for ((ref, info) in b) {
        if (ref.isFieldOf(thisRef)) {
          store.merge(ref, info)
        }
      }
      return store
    }
  }

}
