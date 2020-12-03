package org.checkerframework.checker.jtc.analysis

import org.checkerframework.checker.jtc.typecheck.JTCBottomType
import org.checkerframework.checker.jtc.typecheck.JTCType
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.framework.type.visitor.EquivalentAtmComboScanner
import javax.lang.model.type.TypeMirror

private class AnnotatedTypeMirrorComparer : EquivalentAtmComboScanner<Boolean, Analyzer>() {
  private fun compare(type1: AnnotatedTypeMirror, type2: AnnotatedTypeMirror, analyzer: Analyzer): Boolean {
    return type1 === type2 || analyzer.utils.isSameType(type1.underlyingType, type2.underlyingType)
  }

  override fun scanWithNull(type1: AnnotatedTypeMirror?, type2: AnnotatedTypeMirror?, analyzer: Analyzer): Boolean {
    return type1 === type2
  }

  override fun scan(type1: AnnotatedTypeMirror, type2: AnnotatedTypeMirror, analyzer: Analyzer): Boolean {
    return compare(type1, type2, analyzer) && super.scan(type1, type2, analyzer)
  }

  override fun reduce(r1: Boolean, r2: Boolean): Boolean {
    return r1 && r2
  }

  override fun defaultErrorMessage(type1: AnnotatedTypeMirror, type2: AnnotatedTypeMirror, analyzer: Analyzer): String {
    throw UnsupportedOperationException(listOf("Comparing two different subclasses of AnnotatedTypeMirror.", "type1=$type1", "type2=$type2").joinToString("\n"))
  }
}

private val EQUALITY_COMPARER = AnnotatedTypeMirrorComparer()

class StoreInfo(val analyzer: Analyzer, val jtcType: JTCType, val type: AnnotatedTypeMirror) {

  constructor(prevInfo: StoreInfo, newType: JTCType) : this(prevInfo.analyzer, newType, prevInfo.type)

  val underlyingType: TypeMirror = type.underlyingType

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other !is StoreInfo) return false
    if (jtcType != other.jtcType) return false
    return analyzer.utils.isSameType(underlyingType, other.underlyingType)
    // TODO infinite loop? return EQUALITY_COMPARER.visit(type, other.type, analyzer)
  }

  override fun hashCode(): Int {
    return jtcType.hashCode()
  }

  override fun toString(): String {
    return "StoreInfo{$jtcType, $type}"
  }

  companion object {
    fun merge(a: StoreInfo, b: StoreInfo): StoreInfo {
      val analyzer = a.analyzer
      // TODO val type = analyzer.utils.leastUpperBound(a.underlyingType, b.underlyingType)
      val mostSpecific = analyzer.utils.mostSpecific(a.underlyingType, b.underlyingType)
      return StoreInfo(
        analyzer,
        a.jtcType.leastUpperBound(b.jtcType),
        if (mostSpecific === a.underlyingType) b.type else a.type
        // TODO this breaks the tests: analyzer.utils.createType(type, a.type.isDeclaration)
      )
    }

    fun intersect(a: StoreInfo, b: StoreInfo): StoreInfo {
      val analyzer = a.analyzer
      val mostSpecific = analyzer.utils.mostSpecific(a.underlyingType, b.underlyingType)
      return StoreInfo(
        analyzer,
        a.jtcType.intersect(b.jtcType),
        if (mostSpecific === a.underlyingType) a.type else b.type
      )
    }
  }
}

sealed class Store(private val map: Map<Reference, StoreInfo>) {

  operator fun contains(ref: Reference) = map.contains(ref)
  operator fun get(ref: Reference): StoreInfo? = map[ref]
  operator fun iterator(): Iterator<Map.Entry<Reference, StoreInfo>> = map.iterator()

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    return other is Store && this.map == other.map
  }

  override fun hashCode(): Int {
    return map.hashCode()
  }

  override fun toString(): String {
    return map.toString()
  }

  fun toMutable(): MutableStore {
    return MutableStore(map.toMutableMap())
  }

  open fun toImmutable(): Store {
    return this
  }

  companion object {
    val empty = MutableStore().toImmutable()

    fun merge(a: Store, b: Store): Store {
      if (a === b) return a
      return a.toMutable().merge(b).toImmutable()
    }

    fun mutableMergeFields(a: Store, b: Store): MutableStore {
      val newStore = MutableStore()
      for ((key, info) in a) {
        if (key.isThisField()) {
          newStore[key] = info
        }
      }
      for ((key, info) in b) {
        if (key.isThisField()) {
          newStore.merge(key, info)
        }
      }
      return newStore
    }
  }
}

class MutableStore(private val map: MutableMap<Reference, StoreInfo> = mutableMapOf()) : Store(map) {

  private var mutable = true

  private fun canMutate() {
    if (!mutable) {
      throw RuntimeException("Cannot mutate immutable store")
    }
  }

  operator fun set(ref: Reference, info: StoreInfo) {
    canMutate()
    map[ref] = info
  }

  // pre: canMutate()
  private fun _merge(ref: Reference, info: StoreInfo) {
    map.compute(ref) { _, curr -> if (curr == null) info else StoreInfo.merge(curr, info) }
  }

  fun merge(ref: Reference, info: StoreInfo) {
    canMutate()
    _merge(ref, info)
  }

  fun merge(other: Store): MutableStore {
    canMutate()
    for ((ref, info) in other) {
      _merge(ref, info)
    }
    return this
  }

  fun mergeFields(other: Store): MutableStore {
    for ((ref, info) in other) {
      if (ref.isThisField()) {
        _merge(ref, info)
      }
    }
    return this
  }

  fun intersect(ref: Reference, info: StoreInfo) {
    canMutate()
    map.compute(ref) { _, curr -> if (curr == null) info else StoreInfo.intersect(curr, info) }
  }

  fun remove(ref: Reference): StoreInfo? {
    canMutate()
    return map.remove(ref)
  }

  fun toBottom(): MutableStore {
    canMutate()
    for ((key, value) in map) {
      map[key] = StoreInfo(value, JTCBottomType.SINGLETON)
    }
    return this
  }

  fun invalidate(analyzer: Analyzer): MutableStore {
    canMutate()
    for ((key, value) in map) {
      map[key] = StoreInfo(value, analyzer.getInvalidated(key.type))
    }
    return this
  }

  fun invalidateFields(analyzer: Analyzer): MutableStore {
    canMutate()
    for ((key, value) in map) {
      if (key.isThisField()) {
        map[key] = StoreInfo(value, analyzer.getInvalidated(key.type))
      }
    }
    return this
  }

  fun invalidatePublicFields(analyzer: Analyzer): MutableStore {
    canMutate()
    for ((key, value) in map) {
      if (key.isThisField() && key is FieldAccess && key.isNonPrivate) {
        map[key] = StoreInfo(value, analyzer.getInvalidated(key.type))
      }
    }
    return this
  }

  override fun toImmutable(): Store {
    mutable = false
    return this
  }

}
