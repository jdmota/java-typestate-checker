package jatyc.typestate

import com.sun.tools.javac.code.Symbol
import jatyc.core.JavaType
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import jatyc.core.typesystem.ProtocolSyncSubtyping
import jatyc.typestate.graph.Graph
import jatyc.typestate.graph.State
import jatyc.typestate.graph.DecisionState
import jatyc.typestate.parser.TypestateLexer
import jatyc.typestate.parser.TypestateParser
import jatyc.utils.ClassUtils
import jatyc.utils.MethodUtils
import jatyc.utils.JTCUtils
import java.nio.file.NoSuchFileException
import java.nio.file.Path
import java.nio.file.Paths

class TypestateProcessor(private val utils: JTCUtils) {
  private val graphs: MutableMap<Path, GraphOrError> = HashMap()

  class GraphOrError {
    val graph: Graph?
    val error: TypestateProcessingError?

    constructor(graph: Graph?) {
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
    private fun process(utils: JTCUtils, file: Path): GraphOrError {
      return try {
        GraphOrError(fromPath(utils, file))
      } catch (exp: Exception) {
        GraphOrError(TypestateProcessingError(exp))
      }
    }

    private fun fromPath(utils: JTCUtils, file: Path): Graph? {
      var resolvedFile = file
      val stream = run {
        try {
          CharStreams.fromPath(resolvedFile)
        } catch (exp1: NoSuchFileException) {
          resolvedFile = Paths.get("$file.protocol")
          try {
            CharStreams.fromPath(resolvedFile)
          } catch (exp2: NoSuchFileException) {
            throw exp1 // Throw the first exception
          }
        }
      }
      val lexer = TypestateLexer(stream)
      val tokens = CommonTokenStream(lexer)
      val parser = TypestateParser(tokens)
      parser.errorHandler = BailErrorStrategy()
      val ast = parser.start().ast
      // println(Dot.fromGraph(graph))
      val graph = Graph.fromTypestate(utils, resolvedFile, ast)
      return validateGraph(utils, graph)
    }

    fun fromString(utils: JTCUtils, protocol: String, file: Path): Graph? {
      val stream = CharStreams.fromString(protocol)
      val lexer = TypestateLexer(stream)
      val tokens = CommonTokenStream(lexer)
      val parser = TypestateParser(tokens)
      parser.errorHandler = BailErrorStrategy()
      val ast = parser.start().ast
      // println(Dot.fromGraph(graph))
      val graph = Graph.fromTypestate(utils, file, ast)
      return validateGraph(utils, graph)
    }

    // Validate typestate by itself
    private fun validateGraph(utils: JTCUtils, graph: Graph): Graph? {
      var hasErrors = false

      fun err(text: String, node: TNode) {
        utils.err(text, graph.userPath, node.pos.pos)
        hasErrors = true
      }

      val unused = graph.unusedStates
      if (unused != null) {
        for (node in unused) {
          utils.warn("Unused state", graph.userPath, node.pos.pos)
        }
      }

      val env = graph.getEnv()

      for (state in graph.getAllConcreteStates()) {
        val seen = mutableSetOf<MethodUtils.MethodSymbolWrapper>()
        for ((transition, dest) in state.transitions) {
          val method = utils.methodUtils.methodNodeToMethodSymbol(env, transition, utils.symtab.unknownSymbol)

          if (method.unknownTypes.isNotEmpty()) {
            err("Unknown type${if (method.unknownTypes.size == 1) "" else "s"} ${method.unknownTypes.joinToString(", ")}", transition)
            continue
          }

          if (!seen.add(method)) {
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
              val enumLabels = JavaType.getEnumLabels(classSymbol)
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

    fun validateSubtyping(utils: JTCUtils, element: Symbol.ClassSymbol, graph: Graph, supers: Set<JavaType>): Graph? {
      var hasErrors = false
      for (superType in supers) {
        val superGraph = superType.getGraph()
        if (superGraph != null) {
          val subtyper = ProtocolSyncSubtyping()
          subtyper.subtyping(graph, superGraph, Pair(graph.getInitialState(), superGraph.getInitialState()))
          for (error in subtyper.errors) {
            utils.err(error, element)
            hasErrors = true
          }
        }
      }
      return if (hasErrors) null else graph
    }
  }
}
