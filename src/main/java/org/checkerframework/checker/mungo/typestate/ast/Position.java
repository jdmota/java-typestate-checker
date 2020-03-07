package org.checkerframework.checker.mungo.typestate.ast;

import org.antlr.v4.runtime.Token;

public class Position {

  public final String filename;
  public final int line;
  public final int column;

  public Position(String filename, int line, int column) {
    this.filename = filename;
    this.line = line;
    this.column = column;
  }

  public static Position tokenToPos(Token token) {
    return new Position(token.getTokenSource().getSourceName(), token.getLine(), token.getCharPositionInLine());
  }

}
