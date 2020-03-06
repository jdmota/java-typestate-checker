package org.checkerframework.checker.mungo.typestate.graph;

import org.checkerframework.checker.mungo.typestate.ast.TDecisionNode;
import org.checkerframework.checker.mungo.typestate.ast.TMethodNode;

import java.util.Map;
import java.util.HashMap;

public class Dot {

  private final Graph graph;
  private int decisionUuid;
  private int stateUuid;
  private Map<AbstractState<?, ?>, String> names;
  private StringBuilder builder;

  private Dot(Graph graph) {
    this.graph = graph;
    this.decisionUuid = 1;
    this.stateUuid = 1;
    this.names = new HashMap<>();
    this.builder = new StringBuilder();
  }

  // TODO prefer queue instead of recursion?

  private String handleState(AbstractState<?, ?> s) {
    if (s instanceof EndState) {
      return "end";
    }

    String name = names.get(s);
    if (name != null) {
      // Already saw this state
      return name;
    }
    if (s instanceof DecisionState) {
      DecisionState state = (DecisionState) s;
      name = "decision__" + decisionUuid++;
      names.put(s, name);
      builder.append(name).append("[shape=\"diamond\"]\n");
      for (Map.Entry<TDecisionNode, AbstractState<?, ?>> entry : state.transitions.entrySet()) {
        String dest = handleState(entry.getValue());
        builder.append(name).append(" -> ").append(dest).append("[label=\"").append(entry.getKey().label).append("\"]\n");
      }
      return name;
    }
    if (s instanceof State) {
      State state = (State) s;
      name = state.node.name == null ? "state__" + stateUuid++ : state.node.name;
      names.put(s, name);
      for (Map.Entry<TMethodNode, AbstractState<?, ?>> entry : state.transitions.entrySet()) {
        String dest = handleState(entry.getValue());
        builder.append(name).append(" -> ").append(dest).append("[label=\"").append(entry.getKey().name).append("\\(...\\)\"]\n");
      }
      return name;
    }
    throw new AssertionError("wrong state");
  }

  private String gen() {
    builder.append("digraph {\n");
    String name = handleState(graph.initialState);
    builder.append("start").append("[shape=\"rectangle\"]\n");
    builder.append("start").append(" -> ").append(name).append("\n");
    builder.append("}\n");
    return builder.toString();
  }

  public static String fromGraph(Graph g) {
    return new Dot(g).gen();
  }

}
