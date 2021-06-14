package jatyc.typestate

import org.antlr.v4.runtime.*
import org.antlr.v4.runtime.InputMismatchException
import org.antlr.v4.runtime.misc.ParseCancellationException
import jatyc.utils.JTCUtils
import java.nio.file.NoSuchFileException
import java.nio.file.Paths
import javax.lang.model.element.Element

class TypestateProcessingError(exp: Exception) : Exception(exp) {
  fun format(): String {
    if (cause == null) {
      return "error without cause"
    }
    if (cause is NoSuchFileException) {
      return "Could not find file " + Paths.get(cause.file).fileName
    }
    if (cause is ParseCancellationException) {
      return errorToString(cause)
    }
    cause.printStackTrace()
    return cause.message ?: "error with no message"
  }

  fun report(utils: JTCUtils, element: Element) {
    if (cause is ParseCancellationException) {
      val e = cause.cause as RecognitionException
      val token = e.offendingToken
      val file = token.tokenSource.sourceName
      val pos = token.startIndex
      utils.err(format(), Paths.get(file), pos)
    } else {
      utils.err(format(), element)
    }
  }

  companion object {
    const val serialVersionUID = 0L

    // Adapted from https://github.com/antlr/antlr4/blob/master/runtime/Java/src/org/antlr/v4/runtime/DefaultErrorStrategy.java
    private fun escapeWSAndQuote(_s: String): String {
      var s = _s
      s = s.replace("\n", "\\n")
      s = s.replace("\r", "\\r")
      s = s.replace("\t", "\\t")
      return "'$s'"
    }

    private fun getTokenErrorDisplay(t: Token?): String {
      if (t == null) return "<no token>"
      var s = t.text
      if (s == null) {
        s = if (t.type == Token.EOF) {
          "<EOF>"
        } else {
          "<" + t.type + ">"
        }
      }
      return escapeWSAndQuote(s)
    }

    private fun reportNoViableAlternative(parser: Parser,
                                          e: NoViableAltException): String {
      val tokens = parser.inputStream
      val input: String
      input = if (tokens != null) {
        if (e.startToken.type == Token.EOF) "<EOF>" else tokens.getText(e.startToken, e.offendingToken)
      } else {
        "<unknown input>"
      }
      return "no viable alternative at input " + escapeWSAndQuote(input)
    }

    private fun reportInputMismatch(parser: Parser,
                                    e: InputMismatchException): String {
      return "mismatched input " + getTokenErrorDisplay(e.offendingToken) +
        " expecting " + e.expectedTokens.toString(parser.vocabulary)
    }

    private fun reportFailedPredicate(parser: Parser,
                                      e: FailedPredicateException): String {
      val ruleName = parser.ruleNames[parser.context.ruleIndex]
      return "rule " + ruleName + " " + e.message
    }

    private fun errorToString(exception: ParseCancellationException): String {
      val e = exception.cause as RecognitionException
      val parser = e.recognizer as Parser
      return when (e) {
        is NoViableAltException -> reportNoViableAlternative(parser, e)
        is InputMismatchException -> reportInputMismatch(parser, e)
        is FailedPredicateException -> reportFailedPredicate(parser, e)
        else -> "unknown recognition error"
      }
    }
  }
}
