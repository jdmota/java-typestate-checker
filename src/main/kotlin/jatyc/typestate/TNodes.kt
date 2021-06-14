package jatyc.typestate

sealed class TNode(val pos: Position)

sealed class TRefNode(pos: Position) : TNode(pos) {
  abstract fun stringName(): String
  override fun toString() = stringName()
}

class TMemberNode(pos: Position, val ref: TRefNode, val id: TIdNode) : TRefNode(pos) {
  override fun stringName() = "${ref.stringName()}.${id.stringName()}"
}

class TIdNode(pos: Position, val name: String) : TRefNode(pos) {
  override fun stringName() = name
}

class TDecisionNode(pos: Position, val label: String, /*TRefNode | TStateNode*/val destination: TNode) : TNode(pos)

class TDecisionStateNode(pos: Position, val decisions: List<TDecisionNode>) : TNode(pos)

class TDeclarationNode(pos: Position, val name: String, val states: List<TStateNode>) : TNode(pos)

class TMethodNode(pos: Position, val returnType: TRefNode, val name: String, val args: List<TRefNode>, /*TRefNode | TStateNode | TDecisionStateNode*/val destination: TNode) : TNode(pos) {

  override fun toString(): String {
    return "TMethodNode{${format()}}"
  }

  fun format() = "$returnType $name(${args.joinToString(", ")})"
}

class TStateNode(pos: Position, val name: String?, val methods: List<TMethodNode>, val isDroppable: Boolean) : TNode(pos)

class TPackageNode(pos: Position, val ref: TRefNode) : TNode(pos)

class TImportNode(pos: Position, val ref: TRefNode, val static: Boolean, val star: Boolean) : TNode(pos)

class TTypestateNode(val pkg: TPackageNode?, val imports: List<TImportNode>, val decl: TDeclarationNode) : TNode((pkg
  ?: imports.firstOrNull() ?: decl).pos)
