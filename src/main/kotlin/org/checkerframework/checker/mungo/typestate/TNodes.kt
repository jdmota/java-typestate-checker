package org.checkerframework.checker.mungo.typestate

sealed class TNode(val pos: Position)

class TDecisionNode(pos: Position, val label: String, /*TIdNode | TStateNode*/val destination: TNode) : TNode(pos)

class TDecisionStateNode(pos: Position, val decisions: List<TDecisionNode>) : TNode(pos)

class TDeclarationNode(pos: Position, val name: String, val states: List<TStateNode>) : TNode(pos)

class TIdNode(pos: Position, val name: String) : TNode(pos)

class TMethodNode(pos: Position, val returnType: String, val name: String, val args: List<String>, /*TIdNode | TStateNode | TDecisionStateNode*/val destination: TNode) : TNode(pos) {

  override fun toString(): String {
    return "TMethodNode{${format()}}"
  }

  fun format() = "$returnType $name(${args.joinToString(", ")})"

}

class TStateNode(pos: Position, val name: String?, val methods: List<TMethodNode>) : TNode(pos)
