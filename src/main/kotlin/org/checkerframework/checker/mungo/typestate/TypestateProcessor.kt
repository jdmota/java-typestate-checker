package org.checkerframework.checker.mungo.typestate

import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.checkerframework.checker.mungo.typestate.TNode
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.checker.mungo.typestate.graph.State
import org.checkerframework.checker.mungo.typestate.graph.DecisionState
import org.checkerframework.checker.mungo.typestate.parser.TypestateLexer
import org.checkerframework.checker.mungo.typestate.parser.TypestateParser
import org.checkerframework.checker.mungo.utils.ClassUtils
import org.checkerframework.checker.mungo.utils.MethodUtils
import org.checkerframework.checker.mungo.utils.MungoUtils
import java.nio.file.NoSuchFileException
import java.nio.file.Path
import java.nio.file.Paths

class TypestateProcessor(private val utils: MungoUtils) {
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

  fun getGraph(file: Path): GraphOrError {
    return graphs.computeIfAbsent(file.toAbsolutePath()) { process(utils, it) }
  }

  companion object {
    private fun process(utils: MungoUtils, file: Path): GraphOrError {
      return try {
        GraphOrError(fromPath(utils, file))
      } catch (exp: Exception) {
        GraphOrError(TypestateProcessingError(exp))
      }
    }

    private fun fromPath(utils: MungoUtils, file: Path): Graph {
      var resolvedFile = file
      val stream = run {
        try {
          CharStreams.fromPath(resolvedFile)
        } catch (exp: NoSuchFileException) {
          resolvedFile = Paths.get("$file.protocol")
          CharStreams.fromPath(resolvedFile)
        }
      }
      val lexer = TypestateLexer(stream)
      val tokens = CommonTokenStream(lexer)
      val parser = TypestateParser(tokens)
      parser.errorHandler = BailErrorStrategy()
      val ast = parser.start().ast
      // println(Dot.fromGraph(graph))
      return Graph.fromTypestate(utils, resolvedFile, ast)
    }

    fun validateClassAndGraph(utils: MungoUtils, element: Symbol.ClassSymbol, graph: Graph): Graph? {
      var hasErrors = false

      fun err(text: String, node: TNode) {
        utils.err(text, graph.userPath, node.pos.pos)
        hasErrors = true
      }

      val env = graph.getEnv()
      val methodSymbols = ClassUtils.getNonStaticPublicMethods(element).map {
        utils.methodUtils.wrapMethodSymbol(it)
      }

      for (state in graph.getAllConcreteStates()) {
        val seen = mutableSetOf<MethodUtils.MethodSymbolWrapper>()
        for ((transition, dest) in state.transitions) {
          val method = utils.methodUtils.methodNodeToMethodSymbol(env, transition, element)

          if (method.unknownTypes.isNotEmpty()) {
            err("Unknown type${if (method.unknownTypes.size == 1) "" else "s"} ${method.unknownTypes.joinToString(", ")}", transition)
            continue
          }

          if (seen.add(method)) {
            if (!methodSymbols.any { it == method }) {
              err("Class ${element.name} has no public method for this transition", transition)
            }
          } else {
            err("Duplicate transition", transition)
          }

          when (dest) {
            is State -> if (method.returnsBoolean() || method.returnsEnum()) {
              err("Expected a decision state", transition.destination)
            }
            is DecisionState -> if (method.returnsBoolean()) {
              val booleanLabels = listOf("true", "false")
              val labels = dest.transitions.map { it.key.label }
              if (labels.size != booleanLabels.size || !labels.containsAll(booleanLabels)) {
                err("Expected decision state with two labels (true/false)", transition.destination)
              }
            } else if (method.returnsEnum()) {
              val classSymbol = method.sym.returnType.tsym as Symbol.ClassSymbol
              val enumLabels = ClassUtils.getEnumLabels(classSymbol)
              val labels = dest.transitions.map { it.key.label }
              if (labels.size != enumLabels.size || !labels.containsAll(enumLabels)) {
                err("Expected decision state to include all enumeration labels", transition.destination)
              }
            } else {
              err("Unexpected decision state", transition.destination)
            }
          }
        }
      }

      return if (hasErrors) null else graph
    }
  }
}
