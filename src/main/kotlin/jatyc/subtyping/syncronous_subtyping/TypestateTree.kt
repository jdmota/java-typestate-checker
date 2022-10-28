package jatyc.subtyping.syncronous_subtyping

import jatyc.core.*

class TypestateTree constructor(val jc: JavaType, val ts: JTCType, val children: Set<TypestateTree>) {

  fun isLeaf(): Boolean  { return children.isEmpty()}

  override fun toString(): String {
    return "(" + jc.toString() + ":" + ts.toString() + "[" +  children.map { it.toString() } + "])"
  }
}

object TypestateTreeUtilities{

  fun height(tt: TypestateTree): Int = if(tt.isLeaf()) 0 else 1 + tt.children.maxOf { height(it) }

  fun clss(tts: Set<TypestateTree>): List<JavaType> = tts.map { it.jc }

  fun domain(tt: TypestateTree): List<JavaType> = tt.children.flatMap { domain(it) } + tt.jc

  fun find(j: JavaType, tts: Set<TypestateTree>): TypestateTree? =  tts.find { it.jc == j }

  fun closest(j: JavaType, tt: TypestateTree): TypestateTree? {
    return if(tt.jc !in j.superTypes) null
    else if(tt.isLeaf() || j == tt.jc) tt
    else {
      val end = findClosestSuperClassInDomain(j,tt)
      val path = computePath(end,tt)
      traverse(path,tt)
    }
  }

  private fun findClosestSuperClassInDomain(j: JavaType, tt: TypestateTree): JavaType {
    val dom = domain(tt)
    var curr = j
    while(curr !in dom) curr = curr.directSuperType()!!
    return curr
  }

  private fun computePath(j: JavaType, tt: TypestateTree, path: List<JavaType> = listOf()): List<JavaType> {
    return if(j == tt.jc) path.reversed()
    else return computePath(j.directSuperType()!!, tt, path + j)
  }

  private fun traverse(path: List<JavaType>, tt: TypestateTree): TypestateTree {
    return if(path.isEmpty()) tt
    else traverse(path - path[0], tt.children.find { it.jc == path[0] }!!)
  }
}

object TypestateTreeManager {

  fun upcastTT(tt: TypestateTree, j: JavaType): TypestateTree {
    return if(tt.jc == j) tt
    else upcastTT(TypestateTree(tt.jc.directSuperType()!!, Subtyping.upcast(tt.ts, tt.jc.directSuperType()!!)!!, setOf(tt))!!,j)
  }

  fun downcastTT(tt: TypestateTree, j: JavaType): TypestateTree {
    val cl = TypestateTreeUtilities.closest(j,tt)!!
    return if(tt.jc == cl.jc)  cl
    else TypestateTree(j, Subtyping.downcast(cl.ts, j)!!, setOf())
  }

  fun mergeTT(tt1: TypestateTree, tt2: TypestateTree):TypestateTree = TypestateTree(tt1.jc, JTCUnionType(setOf(tt1.ts,tt2.ts)), (tt1.children.map { it.jc } union tt2.children.map { it.jc }).map { merge(tt1.children, tt2.children, it, tt1.ts, tt2.ts) }.toSet())

  private fun merge(c1: Set<TypestateTree>, c2: Set<TypestateTree>, j: JavaType, t1: JTCType, t2: JTCType): TypestateTree {
    val jcs1 = TypestateTreeUtilities.clss(c1)
    val jcs2 = TypestateTreeUtilities.clss(c2)
    return if(j in jcs1 && j in jcs2) mergeTT(TypestateTreeUtilities.find(j, c1)!!, TypestateTreeUtilities.find(j, c2)!!)
    else if(j in jcs1 && j !in jcs2) mergeTT(TypestateTreeUtilities.find(j, c1)!!, TypestateTree(j, Subtyping.downcast(t2,j)!!, setOf()))
    else mergeTT(TypestateTree(j, Subtyping.downcast(t1,j)!!, setOf()), TypestateTreeUtilities.find(j, c2)!!)
  }
}
