package org.checkerframework.checker.mungo.analysis

import org.checkerframework.checker.mungo.typecheck.MungoBottomType
import org.checkerframework.checker.mungo.typecheck.MungoType
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

class StoreInfo(val analyzer: Analyzer, val mungoType: MungoType, val type: AnnotatedTypeMirror) {

  constructor(prevInfo: StoreInfo, newType: MungoType) : this(prevInfo.analyzer, newType, prevInfo.type)

  val underlyingType: TypeMirror = type.underlyingType

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other !is StoreInfo) return false
    if (mungoType != other.mungoType) return false
    return analyzer.utils.isSameType(underlyingType, other.underlyingType)
    // TODO infinite loop? return EQUALITY_COMPARER.visit(type, other.type, analyzer)
  }

  override fun hashCode(): Int {
    return mungoType.hashCode()
  }

  override fun toString(): String {
    return "StoreInfo{$mungoType, $type}"
  }

  companion object {
    fun merge(a: StoreInfo, b: StoreInfo): StoreInfo {
      val analyzer = a.analyzer
      // TODO val type = analyzer.utils.leastUpperBound(a.underlyingType, b.underlyingType)
      val mostSpecific = analyzer.utils.mostSpecific(a.underlyingType, b.underlyingType)
      return StoreInfo(
        analyzer,
        a.mungoType.leastUpperBound(b.mungoType),
        if (mostSpecific === a.underlyingType) b.type else a.type
        // TODO this breaks the tests: analyzer.utils.createType(type, a.type.isDeclaration)
      )
    }

    fun intersect(a: StoreInfo, b: StoreInfo): StoreInfo {
      val analyzer = a.analyzer
      val mostSpecific = analyzer.utils.mostSpecific(a.underlyingType, b.underlyingType)
      return StoreInfo(
        analyzer,
        a.mungoType.intersect(b.mungoType),
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
      map[key] = StoreInfo(value, MungoBottomType.SINGLETON)
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

sealed class EqualityTracker {

  // If two references are associated with the same integer,
  // that means they are known to point to the same value.

  protected val refToNum = mutableMapOf<Reference, Int>()
  protected val numToRefs = mutableMapOf<Int, MutableSet<Reference>>()

  operator fun get(ref: Reference): Set<Reference> {
    val num = refToNum[ref] ?: return setOf(ref)
    return numToRefs[num]!!
  }

}

class MutableEqualityTracker : EqualityTracker() {

  private var nextNum = 0

  fun setEquality(a: Reference, b: Reference) {
    if (a == b) {
      return
    }
    val aNum = refToNum[a]
    val bNum = refToNum[b]

    when {
      aNum == null && bNum == null -> {
        val newNum = nextNum++
        refToNum[a] = newNum
        refToNum[b] = newNum
        numToRefs[newNum] = mutableSetOf(a, b)
      }
      aNum == null -> {
        refToNum[a] = bNum!!
        numToRefs[bNum]!!.add(a)
      }
      bNum == null -> {
        refToNum[b] = aNum
        numToRefs[aNum]!!.add(b)
      }
      aNum < bNum -> {
        val aSet = numToRefs[aNum]!!
        val bSet = numToRefs.remove(bNum)!!
        for (r in bSet) {
          refToNum[r] = aNum
          aSet.add(r)
        }
      }
      aNum > bNum -> {
        val aSet = numToRefs.remove(aNum)!!
        val bSet = numToRefs[bNum]!!
        for (r in aSet) {
          refToNum[r] = bNum
          bSet.add(r)
        }
      }
    }
  }

  fun invalidate(ref: Reference) {
    val num = refToNum.remove(ref) ?: return
    numToRefs[num]!!.remove(ref)
  }

}
