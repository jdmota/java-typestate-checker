package org.checkerframework.checker.mungo.utils

import com.sun.source.util.TreePath
import com.sun.tools.javac.code.*
import com.sun.tools.javac.processing.JavacProcessingEnvironment
import com.sun.tools.javac.util.List as JavacList
import com.sun.tools.javac.util.Names
import org.checkerframework.checker.mungo.typestate.ast.TMethodNode
import org.checkerframework.javacutil.TypesUtils

class MethodUtils(private val utils: MungoUtils) {

  inner class MethodSymbolWrapper(val sym: Symbol.MethodSymbol, val unknownTypes: List<String> = emptyList()) {

    override fun equals(other: Any?): Boolean {
      if (this === other) return true
      if (other !is MethodSymbolWrapper) return false
      return sameMethod(sym, other.sym)
    }

    override fun hashCode(): Int {
      return sym.name.toString().hashCode()
    }

    override fun toString(): String {
      return sym.toString()
    }

    fun returnsBoolean() = returnsBoolean(sym)
    fun returnsEnum() = returnsEnum(sym)
  }

  private val names = Names.instance((utils.checker.processingEnvironment as JavacProcessingEnvironment).context)
  private val symtab = Symtab.instance((utils.checker.processingEnvironment as JavacProcessingEnvironment).context)
  private val typeUtils = utils.checker.typeUtils
  private val resolver = utils.resolver

  fun wrapMethodSymbol(sym: Symbol.MethodSymbol) = MethodSymbolWrapper(sym)

  fun methodNodeToMethodSymbol(treePath: TreePath, node: TMethodNode, owner: Symbol.ClassSymbol): MethodSymbolWrapper {
    val unknownTypes = mutableListOf<String>()
    fun resolve(type: String): Type {
      val resolved = resolver.resolve(treePath, type)
      return if (resolved == null) {
        unknownTypes.add(type)
        symtab.unknownType
      } else resolved
    }

    val flags = Flags.PUBLIC.toLong();
    val name = names.fromString(node.name)
    val argtypes = JavacList.from(node.args.map { resolve(it) })
    val restype = resolve(node.returnType)
    val thrown = JavacList.nil<Type>() // TODO
    // TODO generics?
    return MethodSymbolWrapper(Symbol.MethodSymbol(
      flags,
      name,
      Type.MethodType(
        argtypes,
        restype,
        thrown,
        symtab.methodClass // Type.MethodType#tsym
      ),
      owner
    ), unknownTypes)
  }

  private fun isSameType(a: Type?, b: Type?): Boolean {
    if (a == null) return b == null
    if (b == null) return false
    // isSameType for methods does not take thrown exceptions into account
    return typeUtils.isSameType(a, b) && isSameTypes(a.thrownTypes, b.thrownTypes)
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

  fun sameMethod(a: Symbol.MethodSymbol, b: Symbol.MethodSymbol): Boolean {
    return a.name.toString() == b.name.toString() && isSameType(a.type, b.type)
  }

  // We could use "typeUtils.isSameType" with the MethodType, but it does not compare thrown types
  private fun sameMethod(tree: TreePath, name: String, type: Type, node: TMethodNode): Boolean {
    // TODO deal with thrownTypes and typeArguments
    return name == node.name &&
      isSameType(type.returnType, resolver.resolve(tree, node.returnType)) &&
      isSameTypes(type.parameterTypes, node.args.map { resolver.resolve(tree, it) }) &&
      isSameTypes(type.thrownTypes, listOf())
  }

  fun sameMethod(tree: TreePath, sym: Symbol.MethodSymbol, node: TMethodNode): Boolean {
    return sameMethod(tree, sym.name.toString(), sym.type, node)
  }

  fun returnsBoolean(method: Symbol.MethodSymbol): Boolean {
    return TypesUtils.isBooleanType(method.returnType)
  }

  fun returnsEnum(method: Symbol.MethodSymbol): Boolean {
    return method.returnType.tsym.isEnum;
  }

}
