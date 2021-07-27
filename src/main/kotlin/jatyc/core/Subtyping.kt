package jatyc.core

object Subtyping {

  fun subtype(a: JTCType, b: JTCType): Boolean {
    val result = when (a) {
      is JTCUnknownType -> b is JTCUnknownType
      is JTCSharedType -> when (b) {
        is JTCUnknownType -> true
        is JTCSharedType -> a.javaType.isSubtype(b.javaType)
        is JTCUnionType -> b.types.any { subtype(a, it) }
        //is JTCIntersectionType -> b.types.all { subtype(a, it) }
        else -> false
      }
      is JTCUnknownStateType -> when (b) {
        is JTCUnknownType -> true
        is JTCUnknownStateType -> a.javaType.isSubtype(b.javaType)
        is JTCUnionType -> b.types.any { subtype(a, it) }
        //is JTCIntersectionType -> b.types.all { subtype(a, it) }
        else -> false
        // is JTCNoProtocolType -> javaType.isSubtype(other.javaType) && !other.exact
      }
      is JTCStateType -> when (b) {
        is JTCUnknownType -> true
        is JTCUnknownStateType -> a.javaType.isSubtype(b.javaType) && (
          a.graph == b.graph || a.graph.getInitialState() == a.state || a.state.isEnd()
          )
        is JTCStateType -> a.javaType.isSubtype(b.javaType) && (
          a.state == b.state ||
            (a.graph.getInitialState() == a.state && b.graph.getInitialState() == b.state) ||
            (a.state.isEnd() && b.state.isEnd())
          )
        is JTCUnionType -> b.types.any { subtype(a, it) }
        //is JTCIntersectionType -> b.types.all { subtype(a, it) }
        else -> false
        // is JTCNoProtocolType -> javaType.isSubtype(other.javaType) && !other.exact
      }
      is JTCPrimitiveType -> when (b) {
        is JTCUnknownType -> true
        is JTCPrimitiveType -> a.javaType.isSubtype(b.javaType)
        is JTCUnionType -> b.types.any { subtype(a, it) }
        //is JTCIntersectionType -> b.types.all { subtype(a, it) }
        else -> false
      }
      is JTCNullType -> when (b) {
        is JTCUnknownType -> true
        is JTCNullType -> true
        is JTCUnionType -> b.types.any { subtype(a, it) }
        //is JTCIntersectionType -> b.types.all { subtype(a, it) }
        else -> false
      }
      is JTCBottomType -> true
      is JTCUnionType -> when (b) {
        is JTCUnknownType -> true
        is JTCUnionType -> a.types.all { itA -> b.types.any { itB -> subtype(itA, itB) } }
        //is JTCIntersectionType -> b.types.all { itB -> a.types.all { itA -> subtype(itA, itB) } }
        else -> a.types.all { itA -> subtype(itA, b) }
      }
      /*is JTCIntersectionType -> when (b) {
        is JTCUnknownType -> true
        is JTCUnionType -> a.types.any { itA -> b.types.any { itB -> subtype(itA, itB) } }
        //is JTCIntersectionType -> b.types.all { itB -> a.types.any { itA -> subtype(itA, itB) } }
        else -> a.types.any { itA -> subtype(itA, b) }
      }*/
    }
    return result
  }

  fun upcast(a: JTCType, b: JTCType): JTCType {
    val bot = JTCBottomType.SINGLETON
    val result = when (a) {
      is JTCUnknownType -> if (b is JTCUnknownType) b else bot
      is JTCSharedType -> when (b) {
        is JTCUnknownType -> b
        is JTCSharedType -> if (a.javaType.isSubtype(b.javaType)) b else bot
        is JTCUnionType -> JTCType.createUnion(b.types.map { upcast(a, it) })
        //is JTCIntersectionType -> JTCType.createIntersection(b.types.map { upcast(a, it) })
        else -> bot
      }
      is JTCUnknownStateType -> when (b) {
        is JTCUnknownType -> b
        is JTCUnknownStateType -> if (a.javaType.isSubtype(b.javaType)) b else bot
        is JTCUnionType -> JTCType.createUnion(b.types.map { upcast(a, it) })
        //is JTCIntersectionType -> JTCType.createIntersection(b.types.map { upcast(a, it) })
        else -> bot
      }
      is JTCStateType -> when (b) {
        is JTCUnknownType -> b
        is JTCUnknownStateType -> if (a.javaType.isSubtype(b.javaType)) {
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
        //is JTCIntersectionType -> JTCType.createIntersection(b.types.map { upcast(a, it) })
        else -> bot
      }
      is JTCPrimitiveType -> when (b) {
        is JTCUnknownType -> b
        is JTCPrimitiveType -> if (a.javaType.isSubtype(b.javaType)) b else bot
        is JTCUnionType -> JTCType.createUnion(b.types.map { upcast(a, it) })
        //s JTCIntersectionType -> JTCType.createIntersection(b.types.map { upcast(a, it) })
        else -> bot
      }
      is JTCNullType -> when (b) {
        is JTCUnknownType -> b
        is JTCNullType -> b
        is JTCUnionType -> JTCType.createUnion(b.types.map { upcast(a, it) })
        //is JTCIntersectionType -> JTCType.createIntersection(b.types.map { upcast(a, it) })
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
        /*is JTCIntersectionType -> {
          // b.types.all { itB -> a.types.all { itA -> subtype(itA, itB) } }
          val newTypes = b.types.map { itB -> JTCType.createIntersection(b.types.map { itA -> upcast(itA, itB) }) }
          if (newTypes.contains(bot)) bot else JTCType.createUnion(newTypes)
        }*/
        else -> {
          // a.types.all { itA -> subtype(itA, b) }
          val newTypes = a.types.map { itA -> upcast(itA, b) }
          if (newTypes.contains(bot)) bot else JTCType.createUnion(newTypes)
        }
      }
      /*is JTCIntersectionType -> when (b) {
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
      }*/
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
        //is JTCIntersectionType -> JTCType.createIntersection(b.types.map { forceCast(a, it) })
        else -> bot
      }
      is JTCUnknownStateType -> when (b) {
        is JTCUnknownType -> b
        is JTCUnknownStateType -> b
        is JTCUnionType -> JTCType.createUnion(b.types.map { forceCast(a, it) })
        //is JTCIntersectionType -> JTCType.createIntersection(b.types.map { forceCast(a, it) })
        else -> bot
      }
      is JTCStateType -> when (b) {
        is JTCUnknownType -> b
        is JTCUnknownStateType -> when {
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
        //is JTCIntersectionType -> JTCType.createIntersection(b.types.map { forceCast(a, it) })
        else -> bot
      }
      is JTCPrimitiveType -> when (b) {
        is JTCUnknownType -> b
        is JTCPrimitiveType -> b
        is JTCUnionType -> JTCType.createUnion(b.types.map { forceCast(a, it) })
        //is JTCIntersectionType -> JTCType.createIntersection(b.types.map { forceCast(a, it) })
        else -> bot
      }
      is JTCNullType -> when (b) {
        is JTCUnknownType -> b
        is JTCNullType -> b
        is JTCUnionType -> JTCType.createUnion(b.types.map { forceCast(a, it) })
        //is JTCIntersectionType -> JTCType.createIntersection(b.types.map { forceCast(a, it) })
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
        /*is JTCIntersectionType -> {
          // b.types.all { itB -> a.types.all { itA -> subtype(itA, itB) } }
          val newTypes = b.types.map { itB -> JTCType.createIntersection(b.types.map { itA -> forceCast(itA, itB) }) }
          if (newTypes.contains(bot)) bot else JTCType.createUnion(newTypes)
        }*/
        else -> {
          // a.types.all { itA -> subtype(itA, b) }
          val newTypes = a.types.map { itA -> forceCast(itA, b) }
          if (newTypes.contains(bot)) bot else JTCType.createUnion(newTypes)
        }
      }
      /*is JTCIntersectionType -> when (b) {
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
      }*/
    }
    return result
  }

}
