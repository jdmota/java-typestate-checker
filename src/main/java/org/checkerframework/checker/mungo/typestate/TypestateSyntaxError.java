package org.checkerframework.checker.mungo.typestate;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.ParseCancellationException;

public class TypestateSyntaxError {

  // Adapted from https://github.com/antlr/antlr4/blob/master/runtime/Java/src/org/antlr/v4/runtime/DefaultErrorStrategy.java

  private static String escapeWSAndQuote(String s) {
    s = s.replace("\n", "\\n");
    s = s.replace("\r", "\\r");
    s = s.replace("\t", "\\t");
    return "'" + s + "'";
  }

  private static String getTokenErrorDisplay(Token t) {
    if (t == null) return "<no token>";
    String s = t.getText();
    if (s == null) {
      if (t.getType() == Token.EOF) {
        s = "<EOF>";
      } else {
        s = "<" + t.getType() + ">";
      }
    }
    return escapeWSAndQuote(s);
  }

  private static String reportNoViableAlternative(Parser parser,
                                                  NoViableAltException e) {
    TokenStream tokens = parser.getInputStream();
    String input;
    if (tokens != null) {
      if (e.getStartToken().getType() == Token.EOF) input = "<EOF>";
      else input = tokens.getText(e.getStartToken(), e.getOffendingToken());
    } else {
      input = "<unknown input>";
    }
    return "no viable alternative at input " + escapeWSAndQuote(input);
  }

  private static String reportInputMismatch(Parser parser,
                                            InputMismatchException e) {
    return "mismatched input " + getTokenErrorDisplay(e.getOffendingToken()) +
      " expecting " + e.getExpectedTokens().toString(parser.getVocabulary());
  }

  private static String reportFailedPredicate(Parser parser,
                                              FailedPredicateException e) {
    String ruleName = parser.getRuleNames()[parser.getContext().getRuleIndex()];
    return "rule " + ruleName + " " + e.getMessage();
  }

  public static String errorToString(String filename,
                                     ParseCancellationException exception) {
    String msg;
    RecognitionException e = (RecognitionException) exception.getCause();
    Parser parser = (Parser) e.getRecognizer();
    if (e instanceof NoViableAltException) {
      msg = reportNoViableAlternative(parser, (NoViableAltException) e);
    } else if (e instanceof InputMismatchException) {
      msg = reportInputMismatch(parser, (InputMismatchException) e);
    } else if (e instanceof FailedPredicateException) {
      msg = reportFailedPredicate(parser, (FailedPredicateException) e);
    } else {
      msg = "unknown recognition error";
    }
    Token token = e.getOffendingToken();
    return filename + " line " + token.getLine() + ":" + token.getCharPositionInLine() + " " + msg;
  }

}
