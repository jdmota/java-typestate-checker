package jatyc.core

import jatyc.subtyping.syncronous_subtyping.Subtyper

object Subtyping {

  fun subtype(a: JTCType, b: JTCType): Boolean {
    val result = when (a) {
      is JTCUnknownType -> b is JTCUnknownType
      is JTCSharedType -> when (b) {
        is JTCUnknownType -> true
        is JTCSharedType -> a.javaType.isSubtype(b.javaType)
        is JTCUnionType -> b.types.any { subtype(a, it) }
        is JTCIntersectionType -> b.types.all { subtype(a, it) }
        else -> false
      }
      is JTCLinearType -> when (b) {
        is JTCUnknownType -> true
        is JTCLinearType -> a.javaType.isSubtype(b.javaType)
        is JTCUnionType -> b.types.any { subtype(a, it) }
        is JTCIntersectionType -> b.types.all { subtype(a, it) }
        else -> false
        //is JTCNoProtocolType -> javaType.isSubtype(other.javaType) && !other.exact
      }
      is JTCStateType -> when (b) {
        is JTCUnknownType -> true
        is JTCSharedType -> a.javaType.isSubtype(b.javaType) && a.state.canDropHere() // NEW
        is JTCLinearType -> a.javaType.isSubtype(b.javaType) && a.graph == b.graph
        is JTCStateType -> a.javaType.isSubtype(b.javaType) && Subtyper.isSubtype(a.state, b.state)
        is JTCUnionType -> b.types.any { subtype(a, it) }
        is JTCIntersectionType -> b.types.all { subtype(a, it) }
        else -> false
        //is JTCNoProtocolType -> javaType.isSubtype(other.javaType) && !other.exact
      }
      is JTCPrimitiveType -> when (b) {
        is JTCUnknownType -> true
        is JTCPrimitiveType -> a.javaType.isSubtype(b.javaType)
        is JTCUnionType -> b.types.any { subtype(a, it) }
        is JTCIntersectionType -> b.types.all { subtype(a, it) }
        else -> false
      }
      is JTCNullType -> when (b) {
        is JTCUnknownType -> true
        is JTCNullType -> true
        is JTCUnionType -> b.types.any { subtype(a, it) }
        is JTCIntersectionType -> b.types.all { subtype(a, it) }
        else -> false
      }
      is JTCBottomType -> true
      is JTCUnionType -> when (b) {
        is JTCUnknownType -> true
        is JTCUnionType -> a.types.all { itA -> subtype(itA, b) } || b.types.any { itB -> subtype(a, itB) }
        is JTCIntersectionType -> a.types.all { itA -> subtype(itA, b) } || b.types.all { itB -> subtype(a, itB) }
        else -> a.types.all { itA -> subtype(itA, b) }
      }
      is JTCIntersectionType -> when (b) {
        is JTCUnknownType -> true
        is JTCUnionType -> a.types.any { itA -> subtype(itA, b) } || b.types.any { itB -> subtype(a, itB) }
        is JTCIntersectionType -> a.types.any { itA -> subtype(itA, b) } || b.types.all { itB -> subtype(a, itB) }
        else -> a.types.any { itA -> subtype(itA, b) }
      }
    }
    return result
  }

  // pre: type is subtype of Shared{JavaType} | State{JavaType, ?} | Null
  fun upcast(type: JTCType, javaType: JavaType): JTCType {
    return when (type) {
      is JTCUnknownType -> type
      is JTCUnionType -> JTCType.createUnion(type.types.map {
        upcast(it, javaType)
      })
      is JTCIntersectionType -> JTCType.createIntersection(type.types.map {
        upcast(it, javaType)
      })
      is JTCSharedType -> JTCSharedType(javaType)
      is JTCLinearType -> JTCLinearType(javaType, javaType.getGraph()!!)
      is JTCStateType -> {
        val superGraph = javaType.getGraph()
        if (superGraph == null) {
          JTCSharedType(javaType)
        } else {
          JTCType.createIntersection(
            superGraph.getAllConcreteStates()
              .filter { Subtyper.isSubtype(type.state, it) }
              .map { JTCStateType(javaType, superGraph, it) }
          )
        }
      }
      is JTCPrimitiveType -> JTCPrimitiveType(javaType)
      is JTCNullType -> type
      is JTCBottomType -> type
    }
  }

  fun upcast(a: JTCType, b: JTCType): JTCType {
    val bot = JTCBottomType.SINGLETON
    val result = when (a) {
      is JTCUnknownType -> if (b is JTCUnknownType) b else bot
      is JTCSharedType -> when (b) {
        is JTCUnknownType -> b
        is JTCSharedType -> if (a.javaType.isSubtype(b.javaType)) b else bot
        is JTCUnionType -> JTCType.createUnion(b.types.map { upcast(a, it) })
        is JTCIntersectionType -> JTCType.createIntersection(b.types.map { upcast(a, it) })
        else -> bot
      }
      is JTCLinearType -> when (b) {
        is JTCUnknownType -> b
        is JTCLinearType -> if (a.javaType.isSubtype(b.javaType)) b else bot
        is JTCUnionType -> JTCType.createUnion(b.types.map { upcast(a, it) })
        is JTCIntersectionType -> JTCType.createIntersection(b.types.map { upcast(a, it) })
        else -> bot
      }
      is JTCStateType -> when (b) {
        is JTCUnknownType -> b
        is JTCLinearType -> if (a.javaType.isSubtype(b.javaType)) {
          when {
            a.graph == b.graph -> JTCStateType(b.javaType, b.graph, a.state)
            a.graph.getInitialState() == a.state -> JTCStateType(b.javaType, b.graph, b.graph.getInitialState())
            a.state.isEnd() -> JTCStateType(b.javaType, b.graph, b.graph.getEndState())
            else -> bot
          }
        } else bot
        is JTCStateType -> if (a.javaType.isSubtype(b.javaType)) {
          when {
            a.graph == b.graph && a.state == b.state -> b
            a.graph.getInitialState() == a.state && b.graph.getInitialState() == b.state -> JTCStateType(b.javaType, b.graph, b.graph.getInitialState())
            a.state.isEnd() && b.state.isEnd() -> JTCStateType(b.javaType, b.graph, b.graph.getEndState())
            else -> bot
          }
        } else bot
        is JTCUnionType -> JTCType.createUnion(b.types.map { upcast(a, it) })
        is JTCIntersectionType -> JTCType.createIntersection(b.types.map { upcast(a, it) })
        else -> bot
      }
      is JTCPrimitiveType -> when (b) {
        is JTCUnknownType -> b
        is JTCPrimitiveType -> if (a.javaType.isSubtype(b.javaType)) b else bot
        is JTCUnionType -> JTCType.createUnion(b.types.map { upcast(a, it) })
        is JTCIntersectionType -> JTCType.createIntersection(b.types.map { upcast(a, it) })
        else -> bot
      }
      is JTCNullType -> when (b) {
        is JTCUnknownType -> b
        is JTCNullType -> b
        is JTCUnionType -> JTCType.createUnion(b.types.map { upcast(a, it) })
        is JTCIntersectionType -> JTCType.createIntersection(b.types.map { upcast(a, it) })
        else -> bot
      }
      is JTCBottomType -> bot
      is JTCUnionType -> when (b) {
        is JTCUnknownType -> b
        is JTCUnionType -> {
          // a.types.all { itA -> b.types.any { itB -> subtype(itA, itB) } }
          val newTypes = a.types.map { itA -> JTCType.createUnion(b.types.map { itB -> upcast(itA, itB) }) }
          if (newTypes.contains(bot)) bot else JTCType.createUnion(newTypes)
        }
        is JTCIntersectionType -> {
          // b.types.all { itB -> a.types.all { itA -> subtype(itA, itB) } }
          val newTypes = b.types.map { itB -> JTCType.createIntersection(b.types.map { itA -> upcast(itA, itB) }) }
          if (newTypes.contains(bot)) bot else JTCType.createUnion(newTypes)
        }
        else -> {
          // a.types.all { itA -> subtype(itA, b) }
          val newTypes = a.types.map { itA -> upcast(itA, b) }
          if (newTypes.contains(bot)) bot else JTCType.createUnion(newTypes)
        }
      }
      is JTCIntersectionType -> when (b) {
        is JTCUnknownType -> b
        is JTCUnionType -> {
          // a.types.any { itA -> b.types.any { itB -> subtype(itA, itB) } }
          val newTypes = a.types.map { itA -> JTCType.createUnion(b.types.map { itB -> upcast(itA, itB) }) }.filter { it != bot }
          if (newTypes.isEmpty()) bot else JTCType.createIntersection(newTypes)
        }
        is JTCIntersectionType -> {
          // b.types.all { itB -> a.types.any { itA -> subtype(itA, itB) } }
          val newTypes = b.types.map { itB -> JTCType.createUnion(a.types.map { itA -> upcast(itA, itB) }) }.filter { it != bot }
          if (newTypes.contains(bot)) bot else JTCType.createIntersection(newTypes)
        }
        else -> {
          // a.types.any { itA -> subtype(itA, b) }
          val newTypes = a.types.map { itA -> upcast(itA, b) }.filter { it != bot }
          if (newTypes.isEmpty()) bot else JTCType.createIntersection(newTypes)
        }
      }
    }
    return result
  }

  fun forceCast(a: JTCType, b: JTCType): JTCType {
    val bot = JTCBottomType.SINGLETON
    val result = when (a) {
      is JTCUnknownType -> b
      is JTCSharedType -> when (b) {
        is JTCUnknownType -> b
        is JTCSharedType -> b
        is JTCUnionType -> JTCType.createUnion(b.types.map { forceCast(a, it) })
        is JTCIntersectionType -> JTCType.createIntersection(b.types.map { forceCast(a, it) })
        else -> bot
      }
      is JTCLinearType -> when (b) {
        is JTCUnknownType -> b
        is JTCLinearType -> b
        is JTCUnionType -> JTCType.createUnion(b.types.map { forceCast(a, it) })
        is JTCIntersectionType -> JTCType.createIntersection(b.types.map { forceCast(a, it) })
        else -> bot
      }
      is JTCStateType -> when (b) {
        is JTCUnknownType -> b
        is JTCLinearType -> when {
          a.graph == b.graph -> JTCStateType(b.javaType, b.graph, a.state)
          a.graph.getInitialState() == a.state -> JTCStateType(b.javaType, b.graph, b.graph.getInitialState())
          a.state.isEnd() -> JTCStateType(b.javaType, b.graph, b.graph.getEndState())
          else -> bot
        }
        is JTCStateType -> when {
          a.graph == b.graph && a.state == b.state -> b
          a.graph.getInitialState() == a.state && b.graph.getInitialState() == b.state -> JTCStateType(b.javaType, b.graph, b.graph.getInitialState())
          a.state.isEnd() && b.state.isEnd() -> JTCStateType(b.javaType, b.graph, b.graph.getEndState())
          else -> bot
        }
        is JTCUnionType -> JTCType.createUnion(b.types.map { forceCast(a, it) })
        is JTCIntersectionType -> JTCType.createIntersection(b.types.map { forceCast(a, it) })
        else -> bot
      }
      is JTCPrimitiveType -> when (b) {
        is JTCUnknownType -> b
        is JTCPrimitiveType -> b
        is JTCUnionType -> JTCType.createUnion(b.types.map { forceCast(a, it) })
        is JTCIntersectionType -> JTCType.createIntersection(b.types.map { forceCast(a, it) })
        else -> bot
      }
      is JTCNullType -> when (b) {
        is JTCUnknownType -> b
        is JTCNullType -> b
        is JTCUnionType -> JTCType.createUnion(b.types.map { forceCast(a, it) })
        is JTCIntersectionType -> JTCType.createIntersection(b.types.map { forceCast(a, it) })
        else -> bot
      }
      is JTCBottomType -> bot
      is JTCUnionType -> when (b) {
        is JTCUnknownType -> b
        is JTCUnionType -> {
          // a.types.all { itA -> b.types.any { itB -> subtype(itA, itB) } }
          val newTypes = a.types.map { itA -> JTCType.createUnion(b.types.map { itB -> forceCast(itA, itB) }) }
          if (newTypes.contains(bot)) bot else JTCType.createUnion(newTypes)
        }
        is JTCIntersectionType -> {
          // b.types.all { itB -> a.types.all { itA -> subtype(itA, itB) } }
          val newTypes = b.types.map { itB -> JTCType.createIntersection(b.types.map { itA -> forceCast(itA, itB) }) }
          if (newTypes.contains(bot)) bot else JTCType.createUnion(newTypes)
        }
        else -> {
          // a.types.all { itA -> subtype(itA, b) }
          val newTypes = a.types.map { itA -> forceCast(itA, b) }
          if (newTypes.contains(bot)) bot else JTCType.createUnion(newTypes)
        }
      }
      is JTCIntersectionType -> when (b) {
        is JTCUnknownType -> b
        is JTCUnionType -> {
          // a.types.any { itA -> b.types.any { itB -> subtype(itA, itB) } }
          val newTypes = a.types.map { itA -> JTCType.createUnion(b.types.map { itB -> forceCast(itA, itB) }) }.filter { it != bot }
          if (newTypes.isEmpty()) bot else JTCType.createIntersection(newTypes)
        }
        is JTCIntersectionType -> {
          // b.types.all { itB -> a.types.any { itA -> subtype(itA, itB) } }
          val newTypes = b.types.map { itB -> JTCType.createUnion(a.types.map { itA -> forceCast(itA, itB) }) }.filter { it != bot }
          if (newTypes.contains(bot)) bot else JTCType.createIntersection(newTypes)
        }
        else -> {
          // a.types.any { itA -> subtype(itA, b) }
          val newTypes = a.types.map { itA -> forceCast(itA, b) }.filter { it != bot }
          if (newTypes.isEmpty()) bot else JTCType.createIntersection(newTypes)
        }
      }
    }
    return result
  }

}
