package org.checkerframework.checker.mungo.typestate.ast

class TMethodNode(pos: Position, val returnType: String, val name: String, val args: List<String>, /*TIdNode | TStateNode | TDecisionStateNode*/val destination: TNode) : TNode(pos) {

  override fun toString(): String {
    return "TMethodNode{${format()}}"
  }

  fun format() = "$returnType $name(${args.joinToString(", ")})"

}
