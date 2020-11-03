package org.checkerframework.checker.mungo.assertions

import org.checkerframework.checker.mungo.analysis.*

class EqualityTracker(
  private val refToNum: Map<Reference, Int> = emptyMap(),
  private val numToRefs: Map<Int, MutableSet<Reference>> = emptyMap()
) {
  operator fun get(ref: Reference): Set<Reference> {
    val num = refToNum[ref] ?: return setOf(ref)
    return numToRefs[num]!!
  }

  fun toMutable(): MutableEqualityTracker {
    return MutableEqualityTracker(refToNum.toMutableMap(), numToRefs.toMutableMap())
  }

  fun toImmutable(): EqualityTracker {
    return this
  }
}

// If two references are associated with the same integer,
// that means they are known to point to the same value.

class MutableEqualityTracker(
  private val refToNum: MutableMap<Reference, Int> = mutableMapOf(),
  private val numToRefs: MutableMap<Int, MutableSet<Reference>> = mutableMapOf()
) {

  private var nextNum = 0

  operator fun get(ref: Reference): Set<Reference> {
    val num = refToNum[ref] ?: return setOf(ref)
    return numToRefs[num]!!
  }

  operator fun set(a: Reference, b: Reference) {
    setEquality(a, b)
  }

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

  fun toMutable(): MutableEqualityTracker {
    return MutableEqualityTracker(refToNum.toMutableMap(), numToRefs.toMutableMap())
  }

  fun toImmutable(): EqualityTracker {
    return EqualityTracker(refToNum.toMap(), numToRefs.toMap())
  }

}

class Equalities<E>(var root: E, var set: MutableSet<E> = mutableSetOf(root)) {
  override fun toString(): String {
    return "{root=$root, set=$set}"
  }
}

open class GenericEqualityTracker<E>(private val prefer: (E) -> Boolean) {

  protected val data: MutableMap<E, Equalities<E>> = mutableMapOf()

  private fun data(ref: E) = data.computeIfAbsent(ref) { Equalities(it) }

  fun aliases(key: E): Set<E> = data(key).set

  operator fun get(key: E) = data(key).root

  operator fun set(a: E, b: E) {
    if (a == b) {
      return
    }
    val aData = data(a)
    val bData = data(b)

    val (dest, src) = when {
      prefer(aData.root) -> Pair(aData, bData)
      prefer(bData.root) -> Pair(bData, aData)
      aData.set.size <= bData.set.size -> Pair(aData, bData)
      else -> Pair(bData, aData)
    }

    for (it in src.set) {
      data[it] = dest
      dest.set.add(it)
    }
  }

  override fun toString(): String = data.entries.joinToString(", ", "{", "}") {
    "${it.key}=${it.value.root}"
  }

}

class PossibleEquality(val first: Reference, val second: Reference) {
  operator fun component1(): Reference = first
  operator fun component2(): Reference = second

  override fun equals(other: Any?): Boolean {
    return other is PossibleEquality && ((first == other.first && second == other.second) || (first == other.second && second == other.first))
  }

  override fun hashCode(): Int {
    return first.hashCode() + second.hashCode()
  }
}

private fun refType(a: Reference): Int {
  return when (a) {
    is FieldAccess -> 1
    is ThisReference -> 2
    is ClassName -> 3
    is LocalVariable -> 4
    is ParameterVariable -> 5
    is ReturnSpecialVar -> 6
    is OldSpecialVar -> 7
    is NodeRef -> 8
    is UnknownRef -> 9
    is OuterContextRef -> 10
  }
}

private fun compareRefs(a: Reference?, b: Reference?): Int {
  if (a == b) return 0
  if (a == null) return -1
  if (b == null) return 1

  val parentsCompare = compareRefs(a.parent, b.parent)
  if (parentsCompare != 0) return parentsCompare

  val compare = refType(a) - refType(b)
  if (compare != 0) return compare

  val typeCompare = a.typeString.compareTo(b.typeString)
  if (typeCompare != 0) return typeCompare

  return when {
    a is FieldAccess && b is FieldAccess -> a.fieldName.compareTo(b.fieldName)
    a is ThisReference && b is ThisReference -> 0
    a is ClassName && b is ClassName -> 0
    a is LocalVariable && b is LocalVariable -> a.elementName.compareTo(b.elementName).let { if (it == 0) a.ownerName.compareTo(b.ownerName) else it }
    a is ParameterVariable && b is ParameterVariable -> a.elementName.compareTo(b.elementName).let { if (it == 0) a.ownerName.compareTo(b.ownerName) else it }
    a is ReturnSpecialVar && b is ReturnSpecialVar -> 0
    a is OldSpecialVar && b is OldSpecialVar -> compareRefs(a.reference, b.reference)
    a is NodeRef && b is NodeRef -> a.hashCode().compareTo(b.hashCode())
    a is UnknownRef && b is UnknownRef -> 0
    a is OuterContextRef && b is OuterContextRef -> a.hashCode().compareTo(b.hashCode())
    else -> error("Impossible")
  }
}

private fun <T> defaultPrefer(arg: T) = false

class PossibleEqualitiesTracker : GenericEqualityTracker<Reference>(::defaultPrefer) {
  fun getAll(): List<Pair<Reference, Reference>> {
    val seen = mutableSetOf<PossibleEquality>()
    val list = mutableListOf<Pair<Reference, Reference>>()
    for ((ref, equalities) in data) {
      val set = equalities.set
      for (otherRef in set) {
        if (ref !== otherRef) {
          if (seen.add(PossibleEquality(ref, otherRef))) {
            list.add(Pair(ref, otherRef))
          }
        }
      }
    }
    return list
  }
}
