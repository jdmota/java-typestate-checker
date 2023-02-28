package jatyc.typestate.graph

import jatyc.typestate.*

sealed class UnresolvedJavaType {
  companion object {
    fun make(node: TRefNode): UnresolvedJavaType {
      return when (node) {
        is TIdNode -> UnresolvedJavaTypeId(node.name)
        is TMemberNode -> UnresolvedJavaTypeSelect(make(node.ref), node.id.name)
        is TArrayTypeNode -> UnresolvedJavaTypeArray(make(node.ref))
      }
    }
  }

  abstract fun getName(): String
}

class UnresolvedJavaTypeId(val id: String) : UnresolvedJavaType() {
  override fun getName(): String {
    return id
  }

  override fun equals(other: Any?): Boolean {
    return other is UnresolvedJavaTypeId && id == other.id
  }

  override fun hashCode(): Int {
    return id.hashCode()
  }
}

class UnresolvedJavaTypeSelect(val parent: UnresolvedJavaType, val id: String) : UnresolvedJavaType() {
  override fun getName(): String {
    return parent.getName() + "." + id
  }

  override fun equals(other: Any?): Boolean {
    return other is UnresolvedJavaTypeSelect && id == other.id && parent == other.parent
  }

  override fun hashCode(): Int {
    var result = parent.hashCode()
    result = 31 * result + id.hashCode()
    return result
  }
}

class UnresolvedJavaTypeArray(val component: UnresolvedJavaType) : UnresolvedJavaType() {
  override fun getName(): String {
    return component.getName() + "[]"
  }

  override fun equals(other: Any?): Boolean {
    return other is UnresolvedJavaTypeArray && component == other.component
  }

  override fun hashCode(): Int {
    return component.hashCode() * 31
  }
}

sealed class Transition<N : TNode>(val nodes: List<N> = mutableListOf())

class MethodTransition(val returnType: UnresolvedJavaType, val name: String, val args: List<UnresolvedJavaType>, val original: TMethodNode) : Transition<TMethodNode>() {
  // TODO actually resolve the JavaType instead of comparing names
  override fun equals(other: Any?): Boolean {
    return other is MethodTransition && returnType == other.returnType && name == other.name && args == other.args
  }

  override fun hashCode(): Int {
    var result = returnType.hashCode()
    result = 31 * result + name.hashCode()
    result = 31 * result + args.hashCode()
    return result
  }

  companion object {
    fun make(node: TMethodNode): MethodTransition {
      return MethodTransition(
        UnresolvedJavaType.make(node.returnType),
        node.name,
        node.args.map { UnresolvedJavaType.make(it) },
        node
      )
    }
  }
}

class DecisionLabelTransition(val label: String) : Transition<TDecisionNode>() {
  override fun equals(other: Any?): Boolean {
    return other is DecisionLabelTransition && label == other.label
  }

  override fun hashCode(): Int {
    return label.hashCode()
  }

  companion object {
    fun make(node: TDecisionNode): DecisionLabelTransition {
      return DecisionLabelTransition(node.label)
    }
  }
}

private var uuid = 1L

sealed class AbstractState<N : TNode>(var node: N?) {
  abstract fun format(): String
}

open class State private constructor(val name: String, node: TStateNode?) : AbstractState<TStateNode>(node) {
  val id = uuid++

  protected constructor(name: String) : this(name, null)

  constructor(node: TStateNode) : this(node.name ?: "unknown:${node.pos.lineCol}", node)

  private val markedAsDroppable = node != null && node.isDroppable
  val transitions: MutableMap<TMethodNode, AbstractState<*>> = LinkedHashMap()
  val normalizedTransitions: MutableMap<MethodTransition, AbstractState<*>> = LinkedHashMap()

  open fun addTransition(method: TMethodNode, destination: AbstractState<*>) {
    transitions[method] = destination
    normalizedTransitions[MethodTransition.make(method)] = destination
  }

  fun hasTransitions() = transitions.isNotEmpty()

  fun canDropHere() = markedAsDroppable || name == Graph.END_STATE_NAME

  override fun format(): String {
    return name
  }

  override fun toString(): String {
    return if (markedAsDroppable) "State{name=$name, droppable}" else "State{name=$name}"
  }
}

class DecisionState(node: TDecisionStateNode) : AbstractState<TDecisionStateNode>(node) {
  val transitions: MutableMap<TDecisionNode, State> = LinkedHashMap()
  val normalizedTransitions: MutableMap<DecisionLabelTransition, State> = LinkedHashMap()

  fun addTransition(transition: TDecisionNode, destination: State) {
    transitions[transition] = destination
    normalizedTransitions[DecisionLabelTransition.make(transition)] = destination
  }

  override fun format(): String {
    return "<${transitions.map { (t, s) -> "${t.label}: ${s.name}" }.joinToString(", ")}>"
  }

  override fun toString(): String {
    return "DecisionState{node=$node}"
  }
}

class EndState : State(Graph.END_STATE_NAME) {
  override fun addTransition(method: TMethodNode, destination: AbstractState<*>) {
    throw AssertionError("end state should have no transitions")
  }
}

class UnknownState : State("#unknown") {
  override fun addTransition(method: TMethodNode, destination: AbstractState<*>) {
    throw AssertionError("#unknown state should have no transitions")
  }

  override fun format(): String {
    return "?"
  }
}
