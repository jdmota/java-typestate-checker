package org.checkerframework.checker.jtc.typestate

import org.antlr.v4.runtime.Token
import java.nio.file.Paths

class Position(val filename: String, val pos: Int, val line: Int, val column: Int) {
  val basename: String
    get() = Paths.get(filename).fileName.toString()

  val lineCol: String
    get() = "$line:$column"

  override fun toString(): String {
    return "$basename:$lineCol"
  }

  companion object {
    @JvmStatic
    fun tokenToPos(token: Token): Position {
      return Position(token.tokenSource.sourceName, token.startIndex, token.line, token.charPositionInLine)
    }

    val nil = Position("", 0, 1, 0)
  }

}
