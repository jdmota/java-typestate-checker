package org.checkerframework.checker.mungo.typestate

import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.checkerframework.checker.mungo.typestate.ast.TMethodNode
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.checker.mungo.typestate.graph.State
import org.checkerframework.checker.mungo.typestate.graph.DecisionState
import org.checkerframework.checker.mungo.typestate.parser.TypestateLexer
import org.checkerframework.checker.mungo.typestate.parser.TypestateParser
import org.checkerframework.checker.mungo.utils.ClassUtils
import org.checkerframework.checker.mungo.utils.MethodUtils
import org.checkerframework.checker.mungo.utils.MungoUtils
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

    private fun err(utils: MungoUtils, text: String, transition: TMethodNode, state: State, tree: JCTree.JCClassDecl) {
      utils.err("$text transition ${transition.format()} on state ${state.name}", tree)
    }

    fun validateClassAndGraph(utils: MungoUtils, treePath: TreePath, tree: JCTree.JCClassDecl, graph: Graph): Graph {
      val methodTrees = ClassUtils.getNonStaticPublicMethods(tree).map {
        utils.methodUtils.wrapMethodSymbol((it as JCTree.JCMethodDecl).sym)
      }

      for (state in graph.getAllConcreteStates()) {
        val seen = mutableSetOf<MethodUtils.MethodSymbolWrapper>()
        for ((transition, dest) in state.transitions) {
          val method = utils.methodUtils.methodNodeToMethodSymbol(treePath, transition, tree.sym)

          if (method.unknownTypes.isNotEmpty()) {
            err(utils, "Unknown type${if (method.unknownTypes.size == 1) "" else "s"} ${method.unknownTypes.joinToString(", ")} in", transition, state, tree)
            continue
          }

          if (seen.add(method)) {
            if (!methodTrees.any { it == method }) {
              err(utils, "Class has no public method for", transition, state, tree)
            }
          } else {
            err(utils, "Duplicate", transition, state, tree)
          }

          when (dest) {
            is State -> if (method.returnsBoolean() || method.returnsEnum()) {
              err(utils, "Expected a decision state in", transition, state, tree)
            }
            is DecisionState -> if (method.returnsBoolean()) {
              val booleanLabels = listOf("true", "false")
              val labels = dest.transitions.map { it.key.label }
              if (labels.size != booleanLabels.size || !labels.containsAll(booleanLabels)) {
                err(utils, "Expected decision state with two labels (true/false) in", transition, state, tree)
              }
            } else if (method.returnsEnum()) {
              val classSymbol = method.sym.returnType.tsym as Symbol.ClassSymbol
              val enumLabels = ClassUtils.getEnumLabels(classSymbol)
              val labels = dest.transitions.map { it.key.label }
              if (labels.size != enumLabels.size || !labels.containsAll(enumLabels)) {
                err(utils, "Expected decision state to include all enumeration labels in", transition, state, tree)
              }
            } else {
              err(utils, "Unexpected decision state in", transition, state, tree)
            }
          }
        }
      }

      return graph
    }
  }
}
