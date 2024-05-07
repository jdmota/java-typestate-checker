package jatyc.core.typesystem

import jatyc.core.*
import jatyc.core.TypecheckUtils.Companion.canDrop
import jatyc.typestate.graph.Graph
import jatyc.typestate.graph.State

object Subtyping {
  private fun findMapping(aState: State, a: JavaType, b: JavaType): List<State> {
    var subClass = a
    var subTypes = listOf(aState)
    var superTypes = mutableListOf<State>()
    while (subClass != b) {
      val superClass = subClass.getSingleSuperType() ?: return emptyList()
      val graph = superClass.getGraph() ?: return emptyList()
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
      is JTCStateType -> when (b) {
        is JTCUnknownType -> true
        is JTCSharedType -> a.javaType.isSubtype(b.javaType) && a.state.canDropHere()
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
      is JTCLinearArrayType -> {
        when (b) {
          is JTCUnknownType -> true
          is JTCLinearArrayType -> if (b.unknownSize) {
            a.javaType == b.javaType
          } else {
            a == b
          }
          is JTCUnionType -> b.types.any { isSubtype(a, it) }
          is JTCIntersectionType -> b.types.all { isSubtype(a, it) }
          is JTCSharedType -> a.javaType == b.javaType && canDrop(a)
          else -> false
        }
      }
    }
  }

  fun cast(t: JTCType, j: JavaType, doUpcast: Boolean): JTCType {
    return when (t) {
      is JTCUnknownType -> JTCUnknownType.SINGLETON
      is JTCSharedType -> when {
        // Upcast
        t.javaType.isSubtype(j) -> if (doUpcast) JTCSharedType(j) else t
        // Downcast
        j.isSubtype(t.javaType) -> JTCSharedType(j)
        else -> JTCUnknownType.SINGLETON
      }
      is JTCStateType -> when {
        // Upcast
        t.javaType.isSubtype(j) -> {
          if (doUpcast) {
            val graph = j.getGraph()
            if (graph == null) {
              JTCUnknownType.SINGLETON
            } else {
              JTCType.createIntersection(graph.getAllConcreteStates().map { JTCStateType(j, graph, it) }.filter { isSubtype(t, it) })
            }
          } else t
        }
        // Downcast
        j.isSubtype(t.javaType) -> {
          val graph = j.getGraph()
          if (graph == null) {
            JTCUnknownType.SINGLETON
          } else {
            JTCType.createUnion(graph.getAllConcreteStates().map { JTCStateType(j, graph, it) }.filter { isSubtype(it, t) })
          }
        }
        else -> JTCUnknownType.SINGLETON
      }
      is JTCUnionType -> JTCType.createUnion(t.types.map { cast(it, j, doUpcast) })
      is JTCIntersectionType -> JTCType.createIntersection(t.types.map { cast(it, j, doUpcast) })
      is JTCBottomType -> JTCBottomType.SINGLETON
      is JTCPrimitiveType -> t
      is JTCNullType -> t
      is JTCLinearArrayType -> t // TODO
    }
  }

  fun refineIntersection(a: JTCType, b: JTCType): JTCType? {
    if (areExclusive(a, b)) {
      return JTCBottomType.SINGLETON
    }
    if (a is JTCStateType && b is JTCStateType && b.isUnknown()) {
      return attemptDowncast(a, b.javaType, b.graph)
    }
    if (b is JTCStateType && a is JTCStateType && a.isUnknown()) {
      return attemptDowncast(b, a.javaType, a.graph)
    }
    if (a is JTCSharedType && b is JTCStateType && b.isUnknown()) {
      return attemptRefineToDroppable(a, b.javaType, b.graph)
    }
    if (b is JTCSharedType && a is JTCStateType && a.isUnknown()) {
      return attemptRefineToDroppable(b, a.javaType, a.graph)
    }
    return null
  }

  private fun areExclusive(a: JTCType, b: JTCType): Boolean {
    return when (a) {
      is JTCSharedType -> when (b) {
        is JTCPrimitiveType,
        is JTCNullType -> true
        is JTCSharedType -> areNotRelated(a.javaType, b.javaType)
        is JTCStateType -> !b.state.canDropHere() || areNotRelated(a.javaType, b.javaType)
        else -> false
      }
      is JTCStateType -> when (b) {
        is JTCPrimitiveType,
        is JTCNullType -> true
        is JTCSharedType -> !a.state.canDropHere() || areNotRelated(a.javaType, b.javaType)
        is JTCStateType -> areNotRelated(a.javaType, b.javaType)
        else -> false
      }
      is JTCPrimitiveType -> b is JTCNullType || b is JTCSharedType || b is JTCStateType
      is JTCNullType -> b is JTCPrimitiveType || b is JTCSharedType || b is JTCStateType
      else -> false
    }
  }

  private fun attemptDowncast(from: JTCStateType, toJavaType: JavaType, toGraph: Graph): JTCType? {
    // If downcasting...
    if (toJavaType.isSubtype(from.javaType)) {
      return JTCType.createUnion(toGraph.getAllConcreteStates().map { JTCStateType(toJavaType, toGraph, it) }.filter { isSubtype(it, from) })
    }
    return null
  }

  private fun attemptRefineToDroppable(a: JTCSharedType, bJavaType: JavaType, bGraph: Graph): JTCType {
    if (a.javaType.isSubtype(bJavaType)) {
      val graph = a.javaType.getGraph() ?: return JTCBottomType.SINGLETON
      return JTCType.createUnion(
        graph.getAllConcreteStates().filter { it.canDropHere() }.map { JTCStateType(a.javaType, graph, it) }
      )
    }
    if (bJavaType.isSubtype(a.javaType)) {
      return JTCType.createUnion(
        bGraph.getAllConcreteStates().filter { it.canDropHere() }.map { JTCStateType(bJavaType, bGraph, it) }
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
