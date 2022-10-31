package jatyc.core

import jatyc.subtyping.syncronous_subtyping.ProtocolSyncSubtyping
import jatyc.typestate.graph.State

object Subtyping {
  private fun findMapping(aState: State, a: JavaType, b: JavaType): List<State> {
    var subClass = a
    var subTypes = listOf(aState)
    var superTypes = mutableListOf<State>()
    while (subClass != b) {
      val superClass = subClass.directSuperType()!!
      val graph = superClass.getGraph()!!
      for (superState in graph.getAllConcreteStates()) {
        for (subState in subTypes) {
          if (ProtocolSyncSubtyping.isSubtype(subState, superState)) {
            superTypes.add(superState)
          }
        }
      }
      subTypes = superTypes
      superTypes = mutableListOf()
      subClass = superClass
    }
    return subTypes
  }

  fun isSubtype(a: JTCType, b: JTCType): Boolean {
    return when (a) {
      is JTCUnknownType -> b is JTCUnknownType
      is JTCSharedType -> when (b) {
        is JTCUnknownType -> true
        is JTCSharedType -> a.javaType.isSubtype(b.javaType)
        is JTCUnionType -> b.types.any { isSubtype(a, it) }
        is JTCIntersectionType -> b.types.all { isSubtype(a, it) }
        else -> false
      }

      is JTCLinearType -> when (b) {
        is JTCUnknownType -> true
        is JTCLinearType -> a.javaType.isSubtype(b.javaType)
        is JTCUnionType -> b.types.any { isSubtype(a, it) }
        is JTCIntersectionType -> b.types.all { isSubtype(a, it) }
        else -> false
        //is JTCNoProtocolType -> javaType.isSubtype(other.javaType) && !other.exact
      }

      is JTCStateType -> when (b) {
        is JTCUnknownType -> true
        is JTCSharedType -> a.javaType.isSubtype(b.javaType) && a.state.canDropHere() // NEW
        is JTCLinearType -> a.javaType.isSubtype(b.javaType)
        is JTCStateType -> {
          if (a.javaType.isSubtype(b.javaType)) {
            // We need to check subtyping level by level to preserve the soundness of downcast later on
            findMapping(a.state, a.javaType, b.javaType).any { ProtocolSyncSubtyping.isSubtype(it, b.state) }
          } else false
        }
        is JTCUnionType -> b.types.any { isSubtype(a, it) }
        is JTCIntersectionType -> b.types.all { isSubtype(a, it) }
        else -> false
        //is JTCNoProtocolType -> javaType.isSubtype(other.javaType) && !other.exact
      }

      is JTCPrimitiveType -> when (b) {
        is JTCUnknownType -> true
        is JTCPrimitiveType -> a.javaType.isSubtype(b.javaType)
        is JTCUnionType -> b.types.any { isSubtype(a, it) }
        is JTCIntersectionType -> b.types.all { isSubtype(a, it) }
        else -> false
      }

      is JTCNullType -> when (b) {
        is JTCUnknownType -> true
        is JTCNullType -> true
        is JTCUnionType -> b.types.any { isSubtype(a, it) }
        is JTCIntersectionType -> b.types.all { isSubtype(a, it) }
        else -> false
      }

      is JTCBottomType -> true
      is JTCUnionType -> when (b) {
        is JTCUnknownType -> true
        is JTCUnionType -> a.types.all { itA -> isSubtype(itA, b) } || b.types.any { itB -> isSubtype(a, itB) }
        is JTCIntersectionType -> a.types.all { itA -> isSubtype(itA, b) } || b.types.all { itB -> isSubtype(a, itB) }
        else -> a.types.all { itA -> isSubtype(itA, b) }
      }

      is JTCIntersectionType -> when (b) {
        is JTCUnknownType -> true
        is JTCUnionType -> a.types.any { itA -> isSubtype(itA, b) } || b.types.any { itB -> isSubtype(a, itB) }
        is JTCIntersectionType -> a.types.any { itA -> isSubtype(itA, b) } || b.types.all { itB -> isSubtype(a, itB) }
        else -> a.types.any { itA -> isSubtype(itA, b) }
      }
    }
  }

  fun upcast(t: JTCType, j: JavaType): JTCType {
    return when (t) {
      is JTCUnknownType -> JTCUnknownType.SINGLETON
      is JTCSharedType -> if (t.javaType.isSubtype(j)) JTCSharedType(j) else JTCUnknownType.SINGLETON
      is JTCLinearType -> {
        val graph = j.getGraph()
        if (graph == null) {
          JTCUnknownType.SINGLETON
        } else {
          if (t.javaType.isSubtype(j)) JTCLinearType(j, graph) else JTCUnknownType.SINGLETON
        }
      }

      is JTCStateType -> {
        val graph = j.getGraph()
        if (graph == null) {
          JTCUnknownType.SINGLETON
        } else {
          graph.getAllConcreteStates().map { JTCStateType(j, graph, it) }.filter { isSubtype(t, it) }.let { JTCType.createIntersection(it.toSet()) }
        }
      }

      is JTCUnionType -> JTCType.createUnion(t.types.map { upcast(it, j) }.toSet())
      is JTCIntersectionType -> JTCType.createIntersection(t.types.map { upcast(it, j) }.toSet())
      is JTCBottomType -> JTCBottomType.SINGLETON
      is JTCPrimitiveType -> t
      is JTCNullType -> t
    }
  }

  fun downcast(t: JTCType, j: JavaType): JTCType {
    return when (t) {
      is JTCUnknownType -> JTCUnknownType.SINGLETON
      is JTCSharedType -> if (j.isSubtype(t.javaType)) JTCSharedType(j) else JTCUnknownType.SINGLETON
      is JTCLinearType -> {
        val graph = j.getGraph()
        if (graph == null) {
          JTCUnknownType.SINGLETON
        } else {
          if (j.isSubtype(t.javaType)) JTCLinearType(j, graph) else JTCUnknownType.SINGLETON
        }
      }

      is JTCStateType -> {
        val graph = j.getGraph()
        if (graph == null) {
          JTCUnknownType.SINGLETON
        } else {
          graph.getAllConcreteStates().map { JTCStateType(j, graph, it) }.filter { isSubtype(it, t) }.let { JTCType.createUnion(it.toSet()) }
        }
      }

      is JTCUnionType -> JTCType.createUnion(t.types.map { downcast(it, j) }.toSet())
      is JTCIntersectionType -> JTCType.createIntersection(t.types.map { downcast(it, j) }.toSet())
      is JTCBottomType -> JTCBottomType.SINGLETON
      is JTCPrimitiveType -> t
      is JTCNullType -> t
    }
  }

  fun refineIntersection(a: JTCType, b: JTCType): JTCType? {
    if (areExclusive(a, b)) {
      return JTCBottomType.SINGLETON
    }
    if (a is JTCStateType && b is JTCLinearType) {
      return attemptDowncast(a, b)
    }
    if (a is JTCLinearType && b is JTCStateType) {
      return attemptDowncast(b, a)
    }
    if (a is JTCSharedType && b is JTCLinearType) {
      return attemptRefineToDroppable(a, b)
    }
    if (b is JTCSharedType && a is JTCLinearType) {
      return attemptRefineToDroppable(b, a)
    }
    return null
  }

  private fun areExclusive(a: JTCType, b: JTCType): Boolean {
    return when (a) {
      is JTCSharedType -> when (b) {
        is JTCPrimitiveType,
        is JTCNullType -> true

        is JTCSharedType -> areNotRelated(a.javaType, b.javaType)
        is JTCLinearType -> areNotRelated(a.javaType, b.javaType)
        is JTCStateType -> !b.state.canDropHere() || areNotRelated(a.javaType, b.javaType)
        else -> false
      }

      is JTCLinearType -> when (b) {
        is JTCPrimitiveType,
        is JTCNullType -> true

        is JTCSharedType -> areNotRelated(a.javaType, b.javaType)
        is JTCLinearType -> areNotRelated(a.javaType, b.javaType)
        is JTCStateType -> areNotRelated(a.javaType, b.javaType)
        else -> false
      }

      is JTCStateType -> when (b) {
        is JTCPrimitiveType,
        is JTCNullType -> true

        is JTCSharedType -> !a.state.canDropHere() || areNotRelated(a.javaType, b.javaType)
        is JTCLinearType -> areNotRelated(a.javaType, b.javaType)
        is JTCStateType -> areNotRelated(a.javaType, b.javaType)
        else -> false
      }

      is JTCPrimitiveType -> b is JTCNullType || b is JTCSharedType || b is JTCLinearType || b is JTCStateType
      is JTCNullType -> b is JTCPrimitiveType || b is JTCSharedType || b is JTCLinearType || b is JTCStateType
      else -> false
    }
  }

  private fun attemptDowncast(from: JTCStateType, to: JTCLinearType): JTCType? {
    // If downcasting...
    if (to.javaType.isSubtype(from.javaType)) {
      return JTCType.createUnion(
        to.graph.getAllConcreteStates()
          .filter { ProtocolSyncSubtyping.isSubtype(it, from.state) }
          .map { JTCStateType(to.javaType, to.graph, it) }
      )
    }
    return null
  }

  private fun attemptRefineToDroppable(a: JTCSharedType, b: JTCLinearType): JTCType {
    if (a.javaType.isSubtype(b.javaType)) {
      val graph = a.javaType.getGraph() ?: return JTCBottomType.SINGLETON
      return JTCType.createUnion(
        graph.getAllConcreteStates().filter { it.canDropHere() }.map { JTCStateType(a.javaType, graph, it) }
      )
    }
    if (b.javaType.isSubtype(a.javaType)) {
      return JTCType.createUnion(
        b.graph.getAllConcreteStates().filter { it.canDropHere() }.map { JTCStateType(b.javaType, b.graph, it) }
      )
    }
    return JTCBottomType.SINGLETON
  }

  private fun areNotRelated(a: JavaType, b: JavaType): Boolean {
    // Two types are not related if they are not subtypes of one another
    // And if one of them is final
    // This means that the intersection of both must be empty
    return !a.isSubtype(b) && !b.isSubtype(a) && (a.isFinal() || b.isFinal())
  }
}
