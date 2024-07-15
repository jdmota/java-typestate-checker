package jatyc.core.linearmode

import jatyc.core.*
import jatyc.core.cfg.ArrayAccess
import jatyc.core.cfg.Id
import jatyc.core.cfg.IntegerLiteral
import jatyc.core.typesystem.TypeInfo
import jatyc.utils.JTCUtils

// TODO for more precision, store the possible label values instead of just if equal is true or not?
class CasePattern(val condition: Reference, val label: String, val equal: Boolean) {
  fun matchesCondition(wantedCondition: Reference): Boolean {
    return condition == wantedCondition
  }

  fun replaceCondition(from: Reference, to: Reference): CasePattern {
    return if (from == condition) CasePattern(to, label, equal) else this
  }

  fun fixThis(from: Reference, to: Reference): CasePattern {
    return CasePattern(condition.fixThis(from, to), label, equal)
  }

  fun not(original: Reference, negation: Reference): CasePattern {
    return if (original == condition) CasePattern(negation, label, !equal) else this
  }

  private fun matches(wantedLabel: String): Boolean {
    return if (equal) label == wantedLabel else label != wantedLabel
  }

  // If this pattern is associated with the wanted condition, return true iff the label matches
  // Otherwise, return true
  fun withLabel(wantedCondition: Reference, wantedLabel: String): Boolean {
    return condition != wantedCondition || matches(wantedLabel)
  }

  // If this pattern is associated with the wanted condition, return true iff the label does not match
  // Otherwise, return true
  fun withoutLabel(wantedCondition: Reference, wantedLabel: String): Boolean {
    return condition != wantedCondition || !matches(wantedLabel)
  }

  fun implies(other: CasePattern): Boolean {
    return condition == other.condition && label == other.label && equal == other.equal
  }

  override fun toString(): String {
    return "#{c=$condition,l=$label,eq=$equal}"
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    return other is CasePattern && condition == other.condition && label == other.label && equal == other.equal
  }

  override fun hashCode(): Int {
    var result = condition.hashCode()
    result = 31 * result + label.hashCode()
    result = 31 * result + equal.hashCode()
    return result
  }
}

class CasePatterns(val list: Set<CasePattern>) {
  fun removeCondition(condition: Reference): CasePatterns? {
    return if (list.any { it.matchesCondition(condition) }) null else this
  }

  fun replaceCondition(from: Reference, to: Reference): CasePatterns {
    return CasePatterns(list.map { it.replaceCondition(from, to) }.toSet())
  }

  fun fixThis(from: Reference, to: Reference): CasePatterns {
    return CasePatterns(list.map { it.fixThis(from, to) }.toSet())
  }

  fun withLabel(condition: Reference, label: String): CasePatterns? {
    val newList = list.filter { it.withLabel(condition, label) }
    return if (newList.size == list.size) this else null
  }

  fun withoutLabel(condition: Reference, label: String): CasePatterns? {
    val newList = list.filter { it.withoutLabel(condition, label) }
    return if (newList.size == list.size) this else null
  }

  fun addCondition(pattern: CasePattern): CasePatterns {
    return CasePatterns(list.plus(pattern))
  }

  fun not(original: Reference, negation: Reference): CasePatterns {
    return CasePatterns(list.map { it.not(original, negation) }.toSet())
  }

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
      return CasePatterns(setOf(CasePattern(condition, label, equal)))
    }

    fun trueCase(): CasePatterns {
      return CasePatterns(setOf())
    }
  }
}

class StoreInfo private constructor(val javaType: JavaType, val cases: Set<Pair<CasePatterns, TypeInfo>>) {
  private fun checkJavaTypeInvariant(javaType: JavaType) {
    if (this.javaType !== javaType) {
      JTCUtils.printStack()
      error("StoreInfo.javaType: expected ${this.javaType} got $javaType")
    }
  }

  val type: TypeInfo get() = toType()
  fun toRegular() = regular(toType())

  private fun mapKeys(fn: (CasePatterns) -> CasePatterns?) = mapKeys(javaType, fn)
  private fun mapKeys(javaType: JavaType, fn: (CasePatterns) -> CasePatterns?) = cases(javaType, cases.mapNotNull {
    val f = fn(it.first)
    if (f != null) Pair(f, it.second) else null
  }.toSet())

  fun mapType(javaType: JavaType, fn: (TypeInfo) -> TypeInfo) = cases(javaType, cases.map { Pair(it.first, fn(it.second)) }.toSet())

  fun isBottom() = cases.isEmpty()

  fun removeCondition(condition: Reference): StoreInfo {
    return mapKeys { it.removeCondition(condition) }
  }

  fun replaceCondition(from: Reference, to: Reference): StoreInfo {
    return mapKeys { it.replaceCondition(from, to) }
  }

  fun addCondition(pattern: CasePattern): StoreInfo {
    return mapKeys { it.addCondition(pattern) }
  }

  fun fixThis(from: Reference, to: Reference): StoreInfo {
    return mapKeys { it.fixThis(from, to) }
  }

  private fun toType(): TypeInfo {
    return TypeInfo.createUnion(javaType, cases.map { it.second })
  }

  fun toShared(): TypeInfo {
    return TypeInfo.createUnion(javaType, cases.map { it.second.toShared() })
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
    checkJavaTypeInvariant(other.javaType)
    return cases(javaType, cases.plus(other.cases))
  }

  // Returns true iff we are sure the information on "this" is contained in the "other"
  // Returns false otherwise
  fun implies(other: StoreInfo): Boolean {
    return cases.all { itA -> other.cases.any { itB -> itA.first.implies(itB.first) && itA.second.isSubtype(itB.second) } }
  }

  fun cast(javaType: JavaType): StoreInfo {
    return StoreInfo(javaType, cases.map { Pair(it.first, it.second.cast(javaType)) }.toSet())
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
    fun regular(type: TypeInfo): StoreInfo {
      return cases(type.javaType, setOf(Pair(CasePatterns.trueCase(), type)))
    }

    fun conditional(condition: Reference, thenInfo: StoreInfo, elseInfo: StoreInfo): StoreInfo {
      thenInfo.checkJavaTypeInvariant(elseInfo.javaType)
      if (thenInfo == elseInfo) {
        return thenInfo
      }
      val truePattern = CasePattern(condition, "true", true)
      val falsePattern = CasePattern(condition, "true", false)
      return thenInfo.and(truePattern).or(elseInfo.and(falsePattern))
    }

    fun conditional(condition: Reference, thenType: TypeInfo, elseType: TypeInfo): StoreInfo {
      return conditional(condition, regular(thenType), regular(elseType))
    }

    fun cases(javaType: JavaType, cases: Set<Pair<CasePatterns, TypeInfo>>): StoreInfo {
      cases.forEach { it.second.checkJavaTypeInvariant(javaType) }
      return StoreInfo(javaType, cases.filter { !it.second.isBottom() }.toSet())
    }

    fun bottom(javaType: JavaType): StoreInfo {
      return StoreInfo(javaType, emptySet())
    }
  }
}

class Store(private val map: MutableMap<Reference, StoreInfo> = mutableMapOf()) {
  // The core functions that use "this.map" directly

  operator fun contains(ref: Reference): Boolean {
    return map.contains(ref)
  }

  fun getOrNull(ref: Reference): StoreInfo? {
    if (ref is CodeExprReference && ref.code is ArrayAccess) {
      val arrayRef = Reference.make(ref.code.array)
      val arrayType = getOrNull(arrayRef) ?: return null
      val intValues = TypecheckUtils.getIntValues(get(Reference.make(ref.code.idx)).type.jtcType) {}
      val elementType = if (intValues == null) {
        TypecheckUtils.arrayGet(arrayType.type.jtcType, null) {}
      } else {
        JTCType.createUnion(intValues.map { TypecheckUtils.arrayGet(arrayType.type.jtcType, it) {} })
      }
      return StoreInfo.regular(TypeInfo.make(ref.javaType, elementType))
    }
    return map[ref]
  }

  operator fun set(ref: Reference, info: StoreInfo) {
    ref.checkJavaTypeInvariant(info.javaType)
    if (ref is CodeExprReference && ref.code is ArrayAccess) {
      val arrayRef = Reference.make(ref.code.array)
      val arrayType = get(arrayRef)
      val intValues = TypecheckUtils.getIntValues(get(Reference.make(ref.code.idx)).type.jtcType) {}
      set(arrayRef, info.mapType(arrayRef.javaType) { typeInfo ->
        val newArrayType = if (intValues == null) {
          TypecheckUtils.arraySet(arrayType.type.jtcType, null, typeInfo.jtcType) {}
        } else {
          JTCType.createUnion(intValues.map { TypecheckUtils.arraySet(arrayType.type.jtcType, it, typeInfo.jtcType) {} })
        }
        TypeInfo.make(arrayRef.javaType, newArrayType)
      })
    } else {
      map[ref] = info
    }
  }

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

  // The functions below do not make use of "this.map" directly

  fun clone(): Store {
    return Store(map.toMutableMap())
  }

  operator fun get(ref: Reference): StoreInfo = getOrNull(ref)
    ?: StoreInfo.regular(TypeInfo.make(ref.javaType, ref.javaType.getDefaultJTCType()))

  operator fun set(ref: Reference, type: TypeInfo) {
    ref.checkJavaTypeInvariant(type.javaType)
    this[ref] = StoreInfo.regular(type)
  }

  fun merge(ref: Reference, info: StoreInfo): Boolean {
    val curr = getOrNull(ref)
    if (curr == null) {
      this[ref] = info
      return true // It changed
    }
    if (info.implies(curr)) {
      return false
    }
    this[ref] = curr.or(info)
    return true // It changed
  }

  fun override(ref: Reference, info: StoreInfo): Boolean {
    val curr = getOrNull(ref)
    if (curr != info) {
      this[ref] = info
      return true // It changed
    }
    return false
  }

  fun hasBottom() = map.any { it.value.isBottom() }

  fun toBottom(): Store {
    for ((ref, _) in this) {
      this[ref] = StoreInfo.bottom(ref.javaType)
    }
    return this
  }

  fun withLabel(condition: Reference, label: String): Store {
    val store = Store()
    for ((ref, info) in this) {
      store[ref] = info.withLabel(condition, label)
    }
    return store
  }

  fun addFact(pattern: CasePattern): Store {
    val store = Store()
    for ((ref, info) in this) {
      store[ref] = info.addCondition(pattern)
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
      store[ref] = info.toShared()
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

  fun overrideTo(other: Store): Boolean {
    var changed = false
    for ((ref, info) in this) {
      changed = other.override(ref, info) || changed
    }
    return changed
  }

  // This function is only used when transferring information about fields
  // between method analyses of a class
  fun fixThis(from: Reference, to: Reference): Store {
    val store = Store()
    for ((ref, info) in this) {
      val newRef = ref.fixThis(from, to)
      if (to === newRef) {
        // Ignore the old "this", as well as any local vars, params, ...
      } else {
        // Keep information about fields on "this"
        store[newRef] = info.fixThis(from, to)
      }
    }
    return store
  }

  fun debugGet(ref: String) = map.filterKeys { it.toString().contains(ref) }.entries.joinToString("\n")

  companion object {
    fun mergeFieldsToNew(a: Store, b: Store, thisRef: Reference): Store {
      val store = a.clone()
      for ((ref, info) in b) {
        if (info.isBottom()) {
          return a.clone()
        }
        if (ref.isFieldOf(thisRef)) {
          store.merge(ref, info)
        }
      }
      return store
    }
  }
}
