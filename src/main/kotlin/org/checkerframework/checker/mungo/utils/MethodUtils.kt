package org.checkerframework.checker.mungo.utils

import com.sun.source.util.TreePath
import com.sun.tools.javac.code.*
import com.sun.tools.javac.processing.JavacProcessingEnvironment
import com.sun.tools.javac.tree.JCTree
import com.sun.tools.javac.tree.TreeMaker
import com.sun.tools.javac.util.List as JavacList
import com.sun.tools.javac.util.Names
import org.checkerframework.checker.mungo.typestate.ast.TMethodNode
import org.checkerframework.javacutil.TypesUtils

class MethodUtils(private val utils: MungoUtils) {

  private val names = Names.instance((utils.checker.processingEnvironment as JavacProcessingEnvironment).context)
  private val symtab = Symtab.instance((utils.checker.processingEnvironment as JavacProcessingEnvironment).context)
  private val typeUtils = utils.checker.typeUtils

  fun methodNodeToMethodSymbol(treePath: TreePath, node: TMethodNode, owner: Symbol): Symbol.MethodSymbol {
    if (owner !is Symbol.ClassSymbol) {
      throw AssertionError("owner should be ClassSymbol not " + owner::class.java)
    }
    val flags = Flags.PUBLIC.toLong();
    val name = names.fromString(node.name)
    val argtypes = JavacList.from(node.args.map { utils.resolve(treePath, it) ?: symtab.unknownType })
    val restype = utils.resolve(treePath, node.returnType) ?: symtab.unknownType
    val thrown = JavacList.nil<Type>() // TODO
    // TODO generics?
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
  private fun sameMethod(tree: TreePath, name: String, type: Type, node: TMethodNode): Boolean {
    // TODO deal with thrownTypes and typeArguments
    return name == node.name &&
      isSameType(type.returnType, utils.resolve(tree, node.returnType)) &&
      isSameTypes(type.parameterTypes, node.args.map { utils.resolve(tree, it) }) &&
      isSameTypes(type.thrownTypes, listOf()) &&
      isSameTypes(type.typeArguments, listOf())
  }

  fun sameMethod(tree: TreePath, sym: Symbol.MethodSymbol, node: TMethodNode): Boolean {
    return sameMethod(tree, sym.name.toString(), sym.type, node)
  }

  fun returnsBoolean(method: Symbol.MethodSymbol): Boolean {
    return TypesUtils.isBooleanType(method.returnType)
  }

  // private val enumType = typeUtils.erasure(symtab.enumSym.type)

  fun returnsEnum(method: Symbol.MethodSymbol): Boolean {
    return method.returnType.tsym.isEnum;
    // return typeUtils.isSubtype(method.returnType, enumType)
  }

}
