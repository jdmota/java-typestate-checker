package org.checkerframework.checker.mungo.typestate.graph;

import org.checkerframework.checker.mungo.typestate.Utils;
import org.checkerframework.checker.mungo.typestate.ast.*;
import org.checkerframework.checker.mungo.typestate.graph.exceptions.DuplicateState;
import org.checkerframework.checker.mungo.typestate.graph.exceptions.ReservedStateName;
import org.checkerframework.checker.mungo.typestate.graph.exceptions.StateNotDefined;
import org.checkerframework.checker.mungo.typestate.graph.exceptions.UnusedStates;

import java.util.*;

public class Graph {

  public static final String END_STATE_NAME = "end";
  public static final List<String> RESERVED_STATE_NAMES = Arrays.asList(END_STATE_NAME);

  public State initialState;
  public State endState;
  private Map<String, State> namedStates;
  private Set<String> referencedStates;

  private Graph() {
    initialState = null;
    endState = new EndState(null);
    namedStates = new HashMap<>();
    referencedStates = new HashSet<>();
  }

  private TStateNode getStateNodeByName(TIdNode id) {
    return getStateByName(id).node;
  }

  private State getStateByName(TIdNode id) {
    State state = namedStates.get(id.name);
    if (state == null) {
      throw new StateNotDefined(id);
    }
    return state;
  }

  private State getStateByNode(TStateNode node) {
    if (node.name == null) {
      return new State(node);
    }
    // namedStates is initialized by the time this is called
    return namedStates.get(node.name);
  }

  private DecisionState getStateByNode(TDecisionStateNode node) {
    return new DecisionState(node);
  }

  private void addNamedState(TStateNode node) {
    if (RESERVED_STATE_NAMES.contains(node.name)) {
      throw new ReservedStateName(node);
    }
    namedStates.compute(node.name, (name, old) -> {
      if (old == null) {
        return new State(node);
      }
      throw new DuplicateState(old.node, node);
    });
  }

  private State traverseState(TStateNode node) {
    // Run this first so that even if the state has no methods, it can be considered as referenced
    boolean traverse = node.name == null || referencedStates.add(node.name);

    if (node.methods.size() == 0) {
      return endState;
    }

    State state = getStateByNode(node);

    if (traverse) {
      for (TMethodNode method : node.methods) {
        state.addTransition(method, traverseDestination(method.destination));
      }
    }

    return state;
  }

  private DecisionState traverseDecision(TDecisionStateNode node) {
    DecisionState state = getStateByNode(node);

    for (TDecisionNode decision : node.decisions) {
      state.addTransition(decision, traverseDestination(decision.destination));
    }

    return state;
  }

  private AbstractState<?, ?> traverseDestination(TNode o) {
    if (o instanceof TIdNode) {
      TIdNode node = ((TIdNode) o);
      if (node.name.equals(END_STATE_NAME)) {
        return endState;
      }
      return traverseState(getStateNodeByName(node));
    }
    if (o instanceof TStateNode)
      return traverseState((TStateNode) o);
    if (o instanceof TDecisionStateNode)
      return traverseDecision((TDecisionStateNode) o);
    throw new AssertionError("wrong destination " + o);
  }

  // TODO use queue instead of recursion? just in case there are like a ton of inner states inside each other
  // TODO minimize?

  private void traverseTypestate(TDeclarationNode node) {
    // If we have no named states, then the end state is also the first one
    if (node.states.size() == 0) {
      initialState = endState;
    } else {
      for (TStateNode state : node.states) {
        addNamedState(state);
      }
      initialState = traverseState(node.states.get(0));
    }

    // Calculate if there are any unused states
    Set<String> unusedStates = new HashSet<>(namedStates.keySet());
    unusedStates.removeAll(referencedStates);

    if (unusedStates.size() > 0) {
      throw new UnusedStates(Utils.map(unusedStates, name -> namedStates.get(name).node));
    }
  }

  public static Graph fromTypestate(TDeclarationNode node) {
    Graph g = new Graph();
    g.traverseTypestate(node);
    return g;
  }

}
