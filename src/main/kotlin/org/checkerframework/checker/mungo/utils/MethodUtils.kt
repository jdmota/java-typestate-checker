package org.checkerframework.checker.mungo.utils

import com.sun.tools.javac.code.*
import com.sun.tools.javac.processing.JavacProcessingEnvironment
import com.sun.tools.javac.tree.JCTree
import com.sun.tools.javac.tree.TreeMaker
import com.sun.tools.javac.util.List
import com.sun.tools.javac.util.Names
import org.checkerframework.checker.mungo.typestate.ast.TMethodNode
import javax.annotation.processing.ProcessingEnvironment

class MethodUtils(env: ProcessingEnvironment) {

  private val names = Names.instance((env as JavacProcessingEnvironment).context)
  private val symtab = Symtab.instance((env as JavacProcessingEnvironment).context)

  // TODO missing stuff
  fun methodNodeToMethodTree(maker: TreeMaker, node: TMethodNode): JCTree.JCMethodDecl {
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
  fun methodNodeToMethodSymbol(node: TMethodNode, owner: Symbol): Symbol.MethodSymbol {
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
