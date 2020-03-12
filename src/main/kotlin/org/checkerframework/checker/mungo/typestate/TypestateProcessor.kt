package org.checkerframework.checker.mungo.typestate

import com.sun.tools.javac.code.Flags
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.code.Symtab
import com.sun.tools.javac.code.Type
import com.sun.tools.javac.tree.JCTree
import com.sun.tools.javac.tree.TreeMaker
import com.sun.tools.javac.util.List
import com.sun.tools.javac.util.Names
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.checkerframework.checker.mungo.typestate.ast.TMethodNode
import org.checkerframework.checker.mungo.typestate.graph.Dot
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.checker.mungo.typestate.parser.TypestateLexer
import org.checkerframework.checker.mungo.typestate.parser.TypestateParser
import java.lang.AssertionError
import java.nio.file.Path
import java.util.*

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
      val graph = Graph.fromTypestate(file, ast)
      println(Dot.fromGraph(graph))
      return graph
    }

    // TODO missing stuff
    fun methodNodeToMethodTree(maker: TreeMaker, names: Names, node: TMethodNode): JCTree.JCMethodDecl {
      val mods = maker.Modifiers(Flags.PUBLIC.toLong());
      val name = names.fromString(node.name)
      val restype = maker.Ident(names.fromString(node.returnType)); // maker.Reference() / maker.Ident() / maker.Literal()
      val typarams: List<JCTree.JCTypeParameter> = List.nil();
      val recvparam: JCTree.JCVariableDecl? = null;
      val params: List<JCTree.JCVariableDecl> = List.nil();
      val thrown: List<JCTree.JCExpression> = List.nil();
      val body: JCTree.JCBlock? = null;
      val defaultValue: JCTree.JCExpression? = null;
      return maker.MethodDef(
        mods,
        name,
        restype,
        typarams,
        recvparam,
        params,
        thrown,
        body,
        defaultValue
      )
    }

    // TODO missing stuff
    fun methodNodeToMethodSymbol(symtab: Symtab, names: Names, node: TMethodNode, owner: Symbol): Symbol.MethodSymbol {
      if (owner !is Symbol.ClassSymbol) {
        throw AssertionError("owner should be ClassSymbol not " + owner::class.java)
      }
      val flags = Flags.PUBLIC.toLong();
      val name = names.fromString(node.name)
      val argtypes = List.nil<Type>()
      val restype = when (node.returnType) {
        "void" -> symtab.voidType
        "boolean" -> symtab.booleanType
        else -> symtab.unknownType
      }
      val thrown = List.nil<Type>()
      // ClassSymbol(1L, names.fromString(""), var1, this.rootPackage)
      return Symbol.MethodSymbol(
        flags,
        name,
        Type.MethodType(
          argtypes,
          restype,
          thrown,
          symtab.methodClass // Type.MethodType#tsym
        ),
        owner
      )
    }
  }
}
