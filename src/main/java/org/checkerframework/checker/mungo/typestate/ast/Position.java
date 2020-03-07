package org.checkerframework.checker.mungo.typestate.ast;

import org.antlr.v4.runtime.Token;

import java.nio.file.Paths;

public class Position {

  public final String filename;
  public final int line;
  public final int column;

  public Position(String filename, int line, int column) {
    this.filename = filename;
    this.line = line;
    this.column = column;
  }

  public String getBasename() {
    return Paths.get(filename).getFileName().toString();
  }

  public String getLineCol() {
    return line + ":" + column;
  }

  @Override
  public String toString() {
    return getBasename() + ":" + getLineCol();
  }

  public static Position tokenToPos(Token token) {
    return new Position(token.getTokenSource().getSourceName(), token.getLine(), token.getCharPositionInLine());
  }

}
