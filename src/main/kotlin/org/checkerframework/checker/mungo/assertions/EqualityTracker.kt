package org.checkerframework.checker.mungo.assertions

import org.checkerframework.checker.mungo.analysis.Reference

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

class Equalities<E>(val root: E, val set: MutableSet<E> = mutableSetOf(root))

class GenericEqualityTracker<E>(private val prefer: (E) -> Boolean) : Map<E, E> {

  private val data: MutableMap<E, Equalities<E>> = mutableMapOf()

  private fun data(ref: E): Equalities<E> {
    return data.computeIfAbsent(ref) { Equalities(it) }
  }

  override operator fun get(key: E): E {
    return data(key).root
  }

  operator fun set(a: E, b: E) {
    if (a == b) {
      return
    }
    val aData = data(a)
    val bData = data(b)

    // If A is preferable as root
    if (prefer(aData.root)) {
      aData.set.addAll(bData.set)
      data[b] = aData
    } else {
      bData.set.addAll(aData.set)
      data[a] = bData
    }
  }

  override val keys: Set<E>
    get() = data.keys
  override val size: Int
    get() = data.size
  override val values: Collection<E>
    get() = TODO("Not yet implemented")
  override val entries: Set<Map.Entry<E, E>>
    get() = TODO("Not yet implemented")

  override fun containsKey(key: E): Boolean {
    return data.containsKey(key)
  }

  override fun containsValue(value: E): Boolean {
    return data[value]?.root == value ?: false
  }

  override fun isEmpty(): Boolean {
    return data.isEmpty()
  }

}
