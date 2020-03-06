package org.checkerframework.checker.mungo.typestate.graph;

import org.checkerframework.checker.mungo.typestate.Utils;
import org.checkerframework.checker.mungo.typestate.ast.*;
import org.checkerframework.checker.mungo.typestate.graph.exceptions.DuplicateState;
import org.checkerframework.checker.mungo.typestate.graph.exceptions.ReservedStateName;
import org.checkerframework.checker.mungo.typestate.graph.exceptions.StateNotDefined;
import org.checkerframework.checker.mungo.typestate.graph.exceptions.UnusedStates;

import java.util.*;
import java.util.stream.Collectors;

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
    namedStates.put(END_STATE_NAME, endState);
    referencedStates = new HashSet<>();
    referencedStates.add("end");
  }

  private TStateNode getStateNodeByName(String name) {
    return getStateByName(name).node;
  }

  private State getStateByName(String name) {
    State state = namedStates.get(name);
    if (state == null) {
      // TODO location
      throw new StateNotDefined(name);
    }
    return state;
  }

  private State getStateByNode(TStateNode node) {
    if (node.name == null) {
      return new State(node);
    }
    return getStateByName(node.name);
  }

  private DecisionState getStateByNode(TDecisionStateNode node) {
    return new DecisionState(node);
  }

  private AbstractState<?, ?> getState(Object o) {
    if (o instanceof String) {
      return getStateByName((String) o);
    }
    if (o instanceof TStateNode) {
      return getStateByNode((TStateNode) o);
    }
    if (o instanceof TDecisionStateNode) {
      return getStateByNode((TDecisionStateNode) o);
    }
    throw new AssertionError("getState");
  }

  private void addNamedState(TStateNode node) {
    if (RESERVED_STATE_NAMES.contains(node.name)) {
      throw new ReservedStateName(node);
    }
    State state = namedStates.compute(node.name, (name, old) -> {
      if (old == null) {
        return new State(node);
      }
      throw new DuplicateState(old.node, node);
    });
    if (initialState == null) {
      initialState = state;
    }
  }

  private State traverseState(TStateNode node) {
    if (node.methods.size() == 0) {
      return endState;
    }

    State state = getStateByNode(node);

    if (node.name == null || referencedStates.add(node.name)) {
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

  private AbstractState<?, ?> traverseDestination(Object o) {
    if (o instanceof String)
      return traverseState(getStateNodeByName((String) o));
    if (o instanceof TStateNode)
      return traverseState((TStateNode) o);
    if (o instanceof TDecisionStateNode)
      return traverseDecision((TDecisionStateNode) o);
    throw new AssertionError("wrong destination " + o);
  }

  private void traverseTypestate(TDeclarationNode node) {
    for (TStateNode state : node.states) {
      addNamedState(state);
    }

    // If we had no named states, then the first state is also the first one
    if (initialState == null) {
      initialState = endState;
    } else {
      traverseState(node.states.get(0));
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
