package jatyc.subtyping.syncronous_subtyping

import jatyc.core.*
import jatyc.core.cfg.MethodCall

class TypestateTree constructor(val jc: JavaType, val ts: JTCType, val children: List<TypestateTree>) {
  fun clss(): Set<JavaType> = children.map { it.jc }.toSet()

  override fun toString(): String {
    return "(" + jc + ":" + ts + "[" + children.map { it.toString() } + "])"
  }
}

object TypestateTreeUtilities {
  fun find(j: JavaType, tts: List<TypestateTree>): TypestateTree? = tts.find { it.jc == j }

  // To build the path from "a" to "b" we start on "b" and go up in the hierarchy and build the path
  private fun path(a: JavaType, b: JavaType): List<JavaType> {
    return if (a == b) {
      emptyList()
    } else {
      path(a, b.directSuperType()!!) + b
    }
  }

  private fun closestByPath(path: List<JavaType>, tt: TypestateTree): TypestateTree {
    return if (path.isEmpty()) {
      tt
    } else {
      val child = find(path.first(), tt.children)
      if (child == null) {
        tt
      } else {
        closestByPath(path.drop(1), child)
      }
    }
  }

  fun closest(j: JavaType, tt: TypestateTree): TypestateTree {
    return closestByPath(path(tt.jc, j), tt)
  }

}

object TypestateTreeManager {
  fun upcastTT(tt: TypestateTree, j: JavaType): TypestateTree {
    return if (tt.jc == j) tt
    else upcastTT(TypestateTree(tt.jc.directSuperType()!!, Subtyping.upcast(tt.ts, tt.jc.directSuperType()!!), listOf(tt)), j)
  }

  fun downcastTT(tt: TypestateTree, j: JavaType): TypestateTree {
    val closest = TypestateTreeUtilities.closest(j, tt)
    return if (tt.jc == closest.jc) closest
    else TypestateTree(j, Subtyping.downcast(closest.ts, j), listOf())
  }

  fun mergeTT(tt1: TypestateTree, tt2: TypestateTree): TypestateTree {
    val classes = tt1.clss() union tt2.clss()
    val newChildren = classes.map { merge(tt1.children, tt2.children, it, tt1.ts, tt2.ts) }
    return TypestateTree(tt1.jc, JTCType.createUnion(setOf(tt1.ts, tt2.ts)), newChildren)
  }

  private fun merge(c1: List<TypestateTree>, c2: List<TypestateTree>, j: JavaType, t1: JTCType, t2: JTCType): TypestateTree {
    val inC1 = TypestateTreeUtilities.find(j, c1)
    val inC2 = TypestateTreeUtilities.find(j, c2)
    return if (inC1 != null && inC2 != null) mergeTT(inC1, inC2)
    else if (inC1 != null) mergeTT(inC1, TypestateTree(j, Subtyping.downcast(t2, j), listOf()))
    else if (inC2 != null) mergeTT(TypestateTree(j, Subtyping.downcast(t1, j), listOf()), inC2)
    else error("non well-formed typestate tree")
  }

  fun evolveTT(utils: TypecheckUtils, tt: TypestateTree, call: MethodCall, outputs: (String) -> Boolean): TypestateTree {
    return TypestateTree(tt.jc, utils.refine(tt.ts, call, outputs), tt.children.map { evolveTT(utils, tt, call, outputs) })
  }
}
