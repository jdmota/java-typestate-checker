package org.checkerframework.checker.mungo.typestate;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.checkerframework.checker.mungo.typestate.ast.TDeclarationNode;
import org.checkerframework.checker.mungo.typestate.graph.Graph;
import org.checkerframework.checker.mungo.typestate.graph.exceptions.TypestateError;

import java.io.IOException;
import java.nio.file.Path;

public class TypestateProcessor {

  public static Graph fromPath(Path file) throws IOException, ParseCancellationException, TypestateError {

    TypestateLexer lexer = new TypestateLexer(CharStreams.fromPath(file));

    CommonTokenStream tokens = new CommonTokenStream(lexer);

    TypestateParser parser = new TypestateParser(tokens);
    parser.setErrorHandler(new BailErrorStrategy());

    TDeclarationNode ast = parser.typestate_declaration().ast;

    return Graph.fromTypestate(ast);
  }

}
