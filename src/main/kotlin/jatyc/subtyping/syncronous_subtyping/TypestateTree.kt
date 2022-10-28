package jatyc.subtyping.syncronous_subtyping

import jatyc.core.JTCType
import jatyc.core.JavaType

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

  /*fun upcastTT(tt: TypestateTree, target: JavaType) {
    return if(tt.jc == target) tt
    else upcastTT(TypestateTree(tt.jc.directSuperType(), upcast))
  }*/
}
