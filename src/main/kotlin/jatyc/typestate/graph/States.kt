package jatyc.typestate.graph

import jatyc.typestate.*

sealed class JavaType {
  companion object {
    fun make(node: TRefNode): JavaType {
      return when (node) {
        is TIdNode -> JavaTypeId(node.name)
        is TMemberNode -> JavaTypeSelect(make(node.ref), node.id.name)
      }
    }
  }

  abstract fun getName(): String
}

class JavaTypeId(val id: String) : JavaType() {
  override fun getName(): String {
    return id
  }

  override fun equals(other: Any?): Boolean {
    return other is JavaTypeId && id == other.id
  }

  override fun hashCode(): Int {
    return id.hashCode()
  }
}

class JavaTypeSelect(val parent: JavaType, val id: String) : JavaType() {
  override fun getName(): String {
    return parent.getName() + "." + id
  }

  override fun equals(other: Any?): Boolean {
    return other is JavaTypeSelect && id == other.id && parent == other.parent
  }

  override fun hashCode(): Int {
    var result = parent.hashCode()
    result = 31 * result + id.hashCode()
    return result
  }
}

sealed class Transition<N : TNode>(val nodes: List<N> = mutableListOf())

class MethodTransition(val returnType: JavaType, val name: String, val args: List<JavaType>) : Transition<TMethodNode>() {
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
        JavaType.make(node.returnType),
        node.name,
        node.args.map { JavaType.make(it) }
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

  val isDroppable = node != null && node.isDroppable

  val transitions: MutableMap<TMethodNode, AbstractState<*>> = LinkedHashMap()
  val normalizedTransitions: MutableMap<MethodTransition, AbstractState<*>> = LinkedHashMap()

  open fun addTransition(method: TMethodNode, destination: AbstractState<*>) {
    transitions[method] = destination
    normalizedTransitions[MethodTransition.make(method)] = destination
  }

  fun isEnd() = normalizedTransitions.isEmpty()

  fun canEndHere() = isDroppable || isEnd()

  override fun format(): String {
    return name
  }

  override fun toString(): String {
    return if (isDroppable) "State{name=$name, droppable}" else "State{name=$name}"
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

class EndState : State("end") {
  override fun addTransition(method: TMethodNode, destination: AbstractState<*>) {
    throw AssertionError("end state should have no transitions")
  }
}
