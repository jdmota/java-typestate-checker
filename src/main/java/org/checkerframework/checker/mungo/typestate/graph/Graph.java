package org.checkerframework.checker.mungo.typestate.graph;

import org.checkerframework.checker.mungo.typestate.Utils;
import org.checkerframework.checker.mungo.typestate.ast.*;
import org.checkerframework.checker.mungo.typestate.graph.exceptions.DuplicateState;
import org.checkerframework.checker.mungo.typestate.graph.exceptions.ReservedStateName;
import org.checkerframework.checker.mungo.typestate.graph.exceptions.StateNotDefined;
import org.checkerframework.checker.mungo.typestate.graph.exceptions.UnusedStates;
import org.checkerframework.checker.mungo.typestate.graph.states.AbstractState;
import org.checkerframework.checker.mungo.typestate.graph.states.DecisionState;
import org.checkerframework.checker.mungo.typestate.graph.states.EndState;
import org.checkerframework.checker.mungo.typestate.graph.states.State;
import org.checkerframework.com.google.common.collect.Sets;

import java.nio.file.Path;
import java.util.*;

public class Graph {

  public static final String END_STATE_NAME = "end";
  public static final List<String> RESERVED_STATE_NAMES = Arrays.asList(END_STATE_NAME);

  private final Path file;
  private State initialState;
  private final EndState endState;
  private final Set<State> finalStates;
  private final Map<String, State> namedStates;
  private final Set<String> referencedStates;
  private Set<String> states;

  private Graph(Path file) {
    this.file = file;
    initialState = null;
    endState = new EndState();
    finalStates = Sets.newHashSet(endState);
    namedStates = new HashMap<>();
    referencedStates = new HashSet<>();
    // Initialized in the end
    states = null;
  }

  public Path getFile() {
    return file;
  }

  public State getInitialState() {
    return initialState;
  }

  public Set<String> getStates() {
    return states;
  }

  public Set<State> getFinalStates() {
    return finalStates;
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

    State state = getStateByNode(node);

    if (node.name == null || referencedStates.add(node.name)) {
      if (node.methods.size() == 0) {
        finalStates.add(state);
      }

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

  public static Graph fromTypestate(Path file, TDeclarationNode node) {
    Graph g = new Graph(file);
    g.traverseTypestate(node);
    g.states = new HashSet<>(g.namedStates.keySet());
    return g;
  }

}
