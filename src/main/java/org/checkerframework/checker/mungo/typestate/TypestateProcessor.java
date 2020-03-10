package org.checkerframework.checker.mungo.typestate;

import org.antlr.v4.runtime.*;
import org.checkerframework.checker.mungo.typestate.ast.TDeclarationNode;
import org.checkerframework.checker.mungo.typestate.graph.Dot;
import org.checkerframework.checker.mungo.typestate.graph.Graph;
import org.checkerframework.checker.nullness.qual.Nullable;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;

public class TypestateProcessor {

  private final Map<Path, GraphOrError> graphs;

  public static class GraphOrError {

    public final @Nullable Graph graph;
    public final @Nullable TypestateProcessingError error;

    public GraphOrError(Graph graph) {
      this.graph = graph;
      this.error = null;
    }

    public GraphOrError(TypestateProcessingError error) {
      this.graph = null;
      this.error = error;
    }

  }

  public TypestateProcessor() {
    this.graphs = new HashMap<>();
  }

  public GraphOrError getGraph(Path file) {
    return graphs.computeIfAbsent(file.normalize(), TypestateProcessor::process);
  }

  private static GraphOrError process(Path file) {
    try {
      return new GraphOrError(TypestateProcessor.fromPath(file));
    } catch (Exception exp) {
      return new GraphOrError(new TypestateProcessingError(exp));
    }
  }

  private static Graph fromPath(Path file) throws Exception {

    TypestateLexer lexer = new TypestateLexer(CharStreams.fromPath(file));

    CommonTokenStream tokens = new CommonTokenStream(lexer);

    TypestateParser parser = new TypestateParser(tokens);
    parser.setErrorHandler(new BailErrorStrategy());

    TDeclarationNode ast = parser.typestate_declaration().ast;

    Graph graph = Graph.fromTypestate(ast);
    System.out.println(Dot.fromGraph(graph));
    return graph;
  }

}
