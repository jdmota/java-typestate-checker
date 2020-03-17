package org.checkerframework.checker.mungo.typestate

import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.checker.mungo.typestate.parser.TypestateLexer
import org.checkerframework.checker.mungo.typestate.parser.TypestateParser
import java.nio.file.Path

class TypestateProcessor {
  private val graphs: MutableMap<Path, GraphOrError> = HashMap()

  class GraphOrError {
    val graph: Graph?
    val error: TypestateProcessingError?

    constructor(graph: Graph) {
      this.graph = graph
      error = null
    }

    constructor(error: TypestateProcessingError) {
      graph = null
      this.error = error
    }
  }

  fun lookupGraph(file: Path): Graph {
    val graph = graphs[file]?.graph
    return graph ?: throw AssertionError("no graph for $file")
  }

  fun getGraph(file: Path): GraphOrError {
    return graphs.computeIfAbsent(file.normalize()) { process(it) }
  }

  companion object {
    private fun process(file: Path): GraphOrError {
      return try {
        GraphOrError(fromPath(file))
      } catch (exp: Exception) {
        GraphOrError(TypestateProcessingError(exp))
      }
    }

    @Throws(Exception::class)
    private fun fromPath(file: Path): Graph {
      val lexer = TypestateLexer(CharStreams.fromPath(file))
      val tokens = CommonTokenStream(lexer)
      val parser = TypestateParser(tokens)
      parser.errorHandler = BailErrorStrategy()
      val ast = parser.typestate_declaration().ast
      // println(Dot.fromGraph(graph))
      return Graph.fromTypestate(file, ast)
    }
  }
}
