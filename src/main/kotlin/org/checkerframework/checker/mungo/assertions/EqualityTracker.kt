package org.checkerframework.checker.mungo.assertions

import org.checkerframework.checker.mungo.analysis.*

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

private class PossibleEquality(val first: Reference, val second: Reference) {
  override fun equals(other: Any?): Boolean {
    return other is PossibleEquality && ((first == other.first && second == other.second) || (first == other.second && second == other.first))
  }

  override fun hashCode(): Int {
    return first.hashCode() + second.hashCode()
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
