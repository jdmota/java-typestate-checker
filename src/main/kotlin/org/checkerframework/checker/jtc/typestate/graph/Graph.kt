package org.checkerframework.checker.jtc.typestate.graph

import com.sun.tools.javac.comp.AttrContext
import com.sun.tools.javac.comp.Env
import org.checkerframework.checker.jtc.typestate.*
import org.checkerframework.checker.jtc.utils.JTCUtils
import java.nio.file.Path

class Graph private constructor(val resolvedFile: Path, val typestateName: String) {
  val userPath = JTCUtils.getUserPath(resolvedFile)

  private var env: Env<AttrContext>? = null
  private var initialState: State? = null
  private val endState = EndState()
  private val finalStates = HashSet<State>()
  private val namedStates = HashMap<String, State>() // Does not include "end"
  private val referencedStates = HashSet<String>()
  private val concreteStates = mutableSetOf<State>()
  private val decisionStates = mutableSetOf<DecisionState>()

  init {
    finalStates.add(endState)
  }

  fun getEnv() = env!!

  fun getInitialState() = initialState!!

  fun getFinalStates(): Set<State> = finalStates

  // All non final states
  fun getAllConcreteStates(): Set<State> = concreteStates

  fun getDecisionStates(): Set<DecisionState> = decisionStates

  fun hasStateByName(name: String): Boolean {
    return namedStates[name] != null
  }

  fun isFinalState(name: String): Boolean {
    return name == "end" || namedStates[name]?.transitions?.isEmpty() ?: false
  }

  private fun getStateByName(id: TIdNode): State {
    return namedStates[id.name] ?: throw StateNotDefined(id)
  }

  private fun getStateByNode(node: TStateNode): State {
    return if (node.name == null) {
      State(node)
    } else namedStates[node.name]!!
    // namedStates is initialized by the time this is called
  }

  private fun getStateByNode(node: TDecisionStateNode): DecisionState {
    return DecisionState(node)
  }

  private fun addNamedState(node: TStateNode) {
    if (node.name == null) {
      throw AssertionError("state without name?")
    }
    if (RESERVED_STATE_NAMES.contains(node.name)) {
      throw ReservedStateName(node)
    }
    namedStates.compute(node.name) { _: String?, old: State? ->
      if (old == null) State(node) else throw DuplicateState(old.node!!, node)
    }
  }

  private fun traverseState(node: TStateNode): State {
    val state = getStateByNode(node)
    if (node.name == null || referencedStates.add(node.name)) {
      if (node.methods.isEmpty()) {
        finalStates.add(state)
      } else {
        concreteStates.add(state)
      }
      for (method in node.methods) {
        state.addTransition(method, traverseDestination(method.destination))
      }
    }
    return state
  }

  private fun traverseDecision(node: TDecisionStateNode): DecisionState {
    val state = getStateByNode(node)
    for (decision in node.decisions) {
      state.addTransition(decision, traverseDestination(decision.destination) as State)
    }
    return state
  }

  private fun traverseDestination(node: TNode): AbstractState<*> {
    if (node is TIdNode) {
      return if (node.name == END_STATE_NAME) {
        endState
      } else traverseState(getStateByName(node).node!!)
    }
    if (node is TStateNode) return traverseState(node)
    if (node is TDecisionStateNode) return traverseDecision(node)
    throw AssertionError("wrong destination $node")
  }

  // TODO use queue instead of recursion? just in case there are like a ton of inner states inside each other
  // TODO minimize? while minimizing, we don't want to lose information about states names...

  private fun traverseTypestate(node: TDeclarationNode) {
    // If we have no named states, then the end state is also the first one
    initialState = if (node.states.isEmpty()) {
      endState
    } else {
      for (state in node.states) {
        addNamedState(state)
      }
      traverseState(node.states[0])
    }

    // Calculate if there are any unused states
    val unusedStates: MutableSet<String> = HashSet(namedStates.keys)
    unusedStates.removeAll(referencedStates)
    if (unusedStates.size > 0) {
      throw UnusedStates(unusedStates.map { namedStates[it]!!.node!! })
    }
  }

  companion object {
    const val END_STATE_NAME = "end"
    val RESERVED_STATE_NAMES: List<String> = listOf(END_STATE_NAME)

    fun fromTypestate(utils: JTCUtils, resolvedFile: Path, node: TTypestateNode): Graph {
      val g = Graph(resolvedFile, node.decl.name)
      g.traverseTypestate(node.decl)
      g.env = utils.resolver.createEnv(g.userPath, node) ?: throw EnvCreationError()
      return g
    }
  }
}
