package jatyc.core

import jatyc.subtyping.syncronous_subtyping.ProtocolSyncSubtyping

object Subtyping {

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
        is JTCLinearType -> a.javaType.isSubtype(b.javaType) && a.graph == b.graph
        is JTCStateType -> a.javaType.isSubtype(b.javaType) && ProtocolSyncSubtyping.isSubtype(a.state, b.state)
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

  fun refineIntersection(a: JTCType, b: JTCType): JTCType? {
    if (a is JTCStateType && b is JTCLinearType) {
      return attemptDowncast(a, b)
    }
    if (a is JTCLinearType && b is JTCStateType) {
      return attemptDowncast(b, a)
    }
    return null
  }

  private fun attemptDowncast(from: JTCStateType, to: JTCLinearType): JTCType? {
    // If downcasting...
    if (to.javaType.isSubtype(from.javaType)) {
      return JTCType.createIntersection(
        to.graph.getAllConcreteStates()
          .filter { ProtocolSyncSubtyping.isSubtype(it, from.state) }
          .map { JTCStateType(to.javaType, to.graph, it) }
      )
    }
    return null
  }

}
