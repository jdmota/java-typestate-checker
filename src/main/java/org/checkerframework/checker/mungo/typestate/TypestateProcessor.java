package org.checkerframework.checker.mungo.typestate;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.antlr.v4.runtime.tree.ParseTreeWalker;

import java.io.IOException;
import java.nio.file.Path;

public class TypestateProcessor {

  public static TypestateParser.Typestate_declarationContext fromPath(Path file) throws IOException, ParseCancellationException {

    TypestateLexer lexer = new TypestateLexer(CharStreams.fromPath(file));

    CommonTokenStream tokens = new CommonTokenStream(lexer);

    TypestateParser parser = new TypestateParser(tokens);
    parser.setErrorHandler(new BailErrorStrategy());

    TypestateParser.Typestate_declarationContext tree = parser.typestate_declaration();

    TypestateBaseListener visitor = new TypestateBaseListener();
    ParseTreeWalker.DEFAULT.walk(visitor, tree);

    return tree;
  }

}
