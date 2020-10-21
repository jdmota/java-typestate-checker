package org.checkerframework.checker.mungo.assertions

import org.checkerframework.checker.mungo.analysis.*

private class Equality {

}

private class Node {

  val children = mutableMapOf<Reference, Node>()

}

class EqualitiesGatherer(locations: Set<Reference>) {

  private val roots = mutableMapOf<Reference, Node>()
  private val tracker = MutableEqualityTracker()

  init {
    for (loc in locations) {
      add(loc)
    }
  }

  fun equality(a: Reference, b: Reference) {
    tracker.setEquality(a, b)
  }

  private fun add(ref: Reference): Node {
    return when (ref) {
      is LocalVariable,
      is ThisReference,
      is ClassName,
      is ReturnSpecialVar,
      is OldSpecialVar -> {
        roots.computeIfAbsent(ref) { Node() }
      }
      is FieldAccess -> {
        val parent = add(ref.receiver)
        parent.children.computeIfAbsent(ref) { Node() }
      }
    }
  }

}
