package jatyc.core.linearmode

import jatyc.core.JTCBottomType
import jatyc.core.JTCType
import jatyc.core.JTCUnknownType
import jatyc.core.Reference

sealed class CasePattern {
  abstract fun replaceCondition(from: Reference, to: Reference): CasePattern
  abstract fun fixThis(from: Reference, to: Reference): CasePattern
  abstract fun not(original: Reference, negation: Reference): CasePattern

  // If this pattern is associated with the wanted condition, return true iff the label matches
  // Otherwise, return true
  abstract fun withLabel(wantedCondition: Reference, wantedLabel: String): Boolean

  // If this pattern is associated with the wanted condition, return true iff the label does not match
  // Otherwise, return true
  abstract fun withoutLabel(wantedCondition: Reference, wantedLabel: String): Boolean

  abstract fun implies(other: CasePattern): Boolean
}

object CaseTrue : CasePattern() {
  override fun replaceCondition(from: Reference, to: Reference): CasePattern {
    return this
  }

  override fun fixThis(from: Reference, to: Reference): CasePattern {
    return this
  }

  override fun not(original: Reference, negation: Reference): CasePattern {
    return this
  }

  override fun withLabel(wantedCondition: Reference, wantedLabel: String): Boolean {
    return true
  }

  override fun withoutLabel(wantedCondition: Reference, wantedLabel: String): Boolean {
    return true
  }

  override fun implies(other: CasePattern): Boolean {
    return when (other) {
      is CaseTrue -> true
      is CaseLabeled -> false
    }
  }

  override fun toString(): String {
    return "#{TRUE}"
  }
}

// TODO for more precision, store the possible label values instead of just if equal is true or not
class CaseLabeled(val condition: Reference, val label: String, val equal: Boolean) : CasePattern() {
  override fun replaceCondition(from: Reference, to: Reference): CasePattern {
    return if (from == condition) CaseLabeled(to, label, equal) else this
  }

  override fun fixThis(from: Reference, to: Reference): CasePattern {
    return CaseLabeled(condition.fixThis(from, to), label, equal)
  }

  override fun not(original: Reference, negation: Reference): CasePattern {
    return if (original == condition) CaseLabeled(negation, label, !equal) else this
  }

  private fun matches(wantedLabel: String): Boolean {
    return if (equal) label == wantedLabel else label != wantedLabel
  }

  // If this pattern is associated with the wanted condition, return true iff the label matches
  // Otherwise, return true
  override fun withLabel(wantedCondition: Reference, wantedLabel: String): Boolean {
    return condition != wantedCondition || matches(wantedLabel)
  }

  // If this pattern is associated with the wanted condition, return true iff the label does not match
  // Otherwise, return true
  override fun withoutLabel(wantedCondition: Reference, wantedLabel: String): Boolean {
    return condition != wantedCondition || !matches(wantedLabel)
  }

  override fun implies(other: CasePattern): Boolean {
    return when (other) {
      is CaseTrue -> true
      is CaseLabeled -> condition == other.condition && label == other.label && equal == other.equal
    }
  }

  override fun toString(): String {
    return "#{c=$condition,l=$label,eq=$equal}"
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    return other is CaseLabeled && condition == other.condition && label == other.label && equal == other.equal
  }

  override fun hashCode(): Int {
    var result = condition.hashCode()
    result = 31 * result + label.hashCode()
    result = 31 * result + equal.hashCode()
    return result
  }
}

class CasePatterns(val list: List<CasePattern>) {
  fun replaceCondition(from: Reference, to: Reference): CasePatterns {
    return CasePatterns(list.map { it.replaceCondition(from, to) })
  }

  fun fixThis(from: Reference, to: Reference): CasePatterns {
    return CasePatterns(list.map { it.fixThis(from, to) })
  }

  fun withLabel(condition: Reference, label: String): CasePatterns {
    val newList = list.filter { it.withLabel(condition, label) }
    return if (newList.size < list.size) CasePatterns(emptyList()) else this
  }

  fun withoutLabel(condition: Reference, label: String): CasePatterns {
    val newList = list.filter { it.withoutLabel(condition, label) }
    return if (newList.size < list.size) CasePatterns(emptyList()) else this
  }

  fun addCondition(pattern: CasePattern): CasePatterns {
    return CasePatterns(list.plus(pattern))
  }

  fun not(original: Reference, negation: Reference): CasePatterns {
    return CasePatterns(list.map { it.not(original, negation) })
  }

  fun isPossible() = list.isNotEmpty()

  fun implies(other: CasePatterns): Boolean {
    return other.list.all { itB -> list.any { itA -> itA.implies(itB) } }
  }

  override fun toString(): String {
    return "Patterns{$list}"
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    return other is CasePatterns && list == other.list
  }

  override fun hashCode(): Int {
    return list.hashCode()
  }

  companion object {
    fun labelled(condition: Reference, label: String, equal: Boolean): CasePatterns {
      return CasePatterns(listOf(CaseLabeled(condition, label, equal)))
    }

    fun trueCase(): CasePatterns {
      return CasePatterns(listOf(CaseTrue))
    }
  }
}

class StoreInfo private constructor(val cases: List<Pair<CasePatterns, JTCType>>) {
  val type: JTCType get() = toType()
  fun toRegular() = regular(toType())

  private fun mapKeys(fn: (CasePatterns) -> CasePatterns) = cases(cases.map { Pair(fn(it.first), it.second) })

  fun replaceCondition(from: Reference, to: Reference): StoreInfo {
    return mapKeys { it.replaceCondition(from, to) }
  }

  fun fixThis(from: Reference, to: Reference): StoreInfo {
    return mapKeys { it.fixThis(from, to) }
  }

  fun toType(): JTCType {
    return JTCType.createUnion(cases.map { it.second })
  }

  fun withLabel(condition: Reference, label: String): StoreInfo {
    return mapKeys { it.withLabel(condition, label) }
  }

  fun withoutLabel(condition: Reference, label: String): StoreInfo {
    return mapKeys { it.withoutLabel(condition, label) }
  }

  fun and(pattern: CasePattern): StoreInfo {
    return mapKeys { it.addCondition(pattern) }
  }

  fun not(original: Reference, negation: Reference): StoreInfo {
    return mapKeys { it.not(original, negation) }
  }

  fun or(other: StoreInfo): StoreInfo {
    return cases(cases.plus(other.cases))
  }

  // Returns true iff we are sure the information on "this" is contained in the "other"
  // Returns false otherwise
  fun implies(other: StoreInfo): Boolean {
    return cases.all { itA -> other.cases.any { itB -> itA.first.implies(itB.first) && itA.second.isSubtype(itB.second) } }
  }

  override fun equals(other: Any?): Boolean {
    return other is StoreInfo && cases == other.cases
  }

  override fun hashCode(): Int {
    return cases.hashCode()
  }

  override fun toString(): String {
    return "Cases{$cases}"
  }

  companion object {
    fun regular(type: JTCType): StoreInfo {
      return cases(listOf(Pair(CasePatterns.trueCase(), type)))
    }

    fun conditional(condition: Reference, thenInfo: StoreInfo, elseInfo: StoreInfo): StoreInfo {
      if (thenInfo == elseInfo) {
        return thenInfo
      }
      val truePattern = CaseLabeled(condition, "true", true)
      val falsePattern = CaseLabeled(condition, "true", false)
      return thenInfo.and(truePattern).or(elseInfo.and(falsePattern))
    }

    fun conditional(condition: Reference, thenType: JTCType, elseType: JTCType): StoreInfo {
      return conditional(condition, regular(thenType), regular(elseType))
    }

    fun cases(cases: List<Pair<CasePatterns, JTCType>>): StoreInfo {
      return StoreInfo(cases.filter { it.first.isPossible() && !it.second.isSubtype(JTCBottomType.SINGLETON) })
    }

    val UNKNOWN = regular(JTCUnknownType.SINGLETON)
    val BOTTOM = cases(emptyList())
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
    map[ref] = StoreInfo.regular(type)
  }

  fun merge(ref: Reference, info: StoreInfo): Boolean {
    val curr = map[ref]
    if (curr == null) {
      map[ref] = info
      return true // It changed
    }
    if (info.implies(curr)) {
      return false
    }
    map[ref] = curr.or(info)
    return true // It changed
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

  fun withLabel(condition: Reference, label: String): Store {
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
      store[ref] = info.toType().toShared()
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
