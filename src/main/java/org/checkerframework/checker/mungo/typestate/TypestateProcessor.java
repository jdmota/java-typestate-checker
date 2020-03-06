package org.checkerframework.checker.mungo.typestate;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.checkerframework.checker.mungo.typestate.ast.TDeclarationNode;

import java.io.IOException;
import java.nio.file.Path;

public class TypestateProcessor {

  public static TDeclarationNode fromPath(Path file) throws IOException, ParseCancellationException {

    TypestateLexer lexer = new TypestateLexer(CharStreams.fromPath(file));

    CommonTokenStream tokens = new CommonTokenStream(lexer);

    TypestateParser parser = new TypestateParser(tokens);
    parser.setErrorHandler(new BailErrorStrategy());

    return parser.typestate_declaration().ast;
  }

}
