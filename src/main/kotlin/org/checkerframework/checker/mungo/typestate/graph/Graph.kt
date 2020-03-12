package org.checkerframework.checker.mungo.typestate.graph

import org.checkerframework.checker.mungo.typestate.Utils.map
import org.checkerframework.checker.mungo.typestate.ast.*
import org.checkerframework.checker.mungo.typestate.graph.exceptions.DuplicateState
import org.checkerframework.checker.mungo.typestate.graph.exceptions.ReservedStateName
import org.checkerframework.checker.mungo.typestate.graph.exceptions.StateNotDefined
import org.checkerframework.checker.mungo.typestate.graph.exceptions.UnusedStates
import org.checkerframework.checker.mungo.typestate.graph.states.AbstractState
import org.checkerframework.checker.mungo.typestate.graph.states.DecisionState
import org.checkerframework.checker.mungo.typestate.graph.states.EndState
import org.checkerframework.checker.mungo.typestate.graph.states.State
import org.checkerframework.com.google.common.collect.Sets
import java.nio.file.Path
import java.util.*
import java.util.function.Function

class Graph private constructor(val file: Path) {
  private var initialState: State? = null
  private val endState: EndState = EndState()
  private val finalStates: MutableSet<State>
  private val namedStates: MutableMap<String, State>
  private val referencedStates: MutableSet<String?>
  var states: Set<String>? = null

  init {
    finalStates = Sets.newHashSet(endState)
    namedStates = HashMap()
    referencedStates = HashSet()
    // Initialized in the end
    states = null
  }

  fun getInitialState(): State {
    return initialState!!
  }

  fun getFinalStates(): Set<State> {
    return finalStates
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
      state.addTransition(decision, traverseDestination(decision.destination))
    }
    return state
  }

  private fun traverseDestination(node: TNode): AbstractState<*, *> {
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
  // TODO minimize?

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
      throw UnusedStates(map(unusedStates, Function { namedStates[it]!!.node!! }))
    }
  }

  companion object {
    const val END_STATE_NAME = "end"
    val RESERVED_STATE_NAMES: List<String> = Arrays.asList(END_STATE_NAME)

    fun fromTypestate(file: Path, node: TDeclarationNode): Graph {
      val g = Graph(file)
      g.traverseTypestate(node)
      g.states = HashSet(g.namedStates.keys)
      return g
    }
  }
}
