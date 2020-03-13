package org.checkerframework.checker.mungo.utils

import com.sun.tools.javac.code.*
import com.sun.tools.javac.processing.JavacProcessingEnvironment
import com.sun.tools.javac.tree.JCTree
import com.sun.tools.javac.tree.TreeMaker
import com.sun.tools.javac.util.List as JavacList
import com.sun.tools.javac.util.Names
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.typestate.ast.TMethodNode

class MethodUtils(private val checker: MungoChecker) {

  private val names = Names.instance((checker.processingEnvironment as JavacProcessingEnvironment).context)
  private val symtab = Symtab.instance((checker.processingEnvironment as JavacProcessingEnvironment).context)
  private val typeUtils = checker.typeUtils

  // TODO missing stuff
  fun methodNodeToMethodTree(maker: TreeMaker, node: TMethodNode): JCTree.JCMethodDecl {
    val mods = maker.Modifiers(Flags.PUBLIC.toLong());
    val name = names.fromString(node.name)
    val restype = maker.Ident(names.fromString(node.returnType)); // maker.Reference() / maker.Ident() / maker.Literal()
    val typarams: JavacList<JCTree.JCTypeParameter> = JavacList.nil();
    val recvparam: JCTree.JCVariableDecl? = null;
    val params: JavacList<JCTree.JCVariableDecl> = JavacList.nil();
    val thrown: JavacList<JCTree.JCExpression> = JavacList.nil();
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
    val argtypes = JavacList.nil<Type>()
    val restype = when (node.returnType) {
      "void" -> symtab.voidType
      "boolean" -> symtab.booleanType
      else -> symtab.unknownType
    }
    val thrown = JavacList.nil<Type>()
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

  private fun getType(type: String): Type? {
    return when (type) {
      "byte" -> symtab.byteType
      "char" -> symtab.charType
      "short" -> symtab.shortType
      "int" -> symtab.intType
      "long" -> symtab.longType
      "float" -> symtab.floatType
      "double" -> symtab.doubleType
      "boolean" -> symtab.booleanType
      "void" -> symtab.voidType
      "Object" -> symtab.objectType // TODO hack to make iterator example work for now
      else -> null // TODO resolve
    }
  }

  private fun isSameType(a: Type?, b: Type?): Boolean {
    if (a == null) return b == null
    if (b == null) return false
    return typeUtils.isSameType(a, b)
  }

  private fun isSameTypes(aList: List<Type?>, bList: List<Type?>): Boolean {
    if (aList.size != bList.size) {
      return false
    }
    val bIt = bList.iterator()
    for (a in aList) {
      val b = bIt.next()
      if (!isSameType(a, b)) {
        return false
      }
    }
    return true
  }

  // We could use "typeUtils.isSameType" with the MethodType, but it does not compare thrown types
  fun sameMethod(unit: JCTree.JCCompilationUnit, sym: Symbol.MethodSymbol, node: TMethodNode): Boolean {
    // TODO test more and deal with thrownTypes and typeArguments
    return sym.name.toString() == node.name &&
      isSameType(sym.type.returnType, getType(node.returnType)) &&
      isSameTypes(sym.type.parameterTypes, node.args.map { getType(it) }) &&
      isSameTypes(sym.type.thrownTypes, listOf()) &&
      isSameTypes(sym.type.typeArguments, listOf())
  }

}
