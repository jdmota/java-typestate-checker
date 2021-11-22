package jatyc.utils

import com.sun.tools.javac.code.*
import com.sun.tools.javac.comp.AttrContext
import com.sun.tools.javac.comp.Env
import com.sun.tools.javac.processing.JavacProcessingEnvironment
import com.sun.tools.javac.util.Names
import jatyc.typestate.TMethodNode
import kotlin.collections.List
import kotlin.collections.emptyList
import kotlin.collections.map
import kotlin.collections.mutableListOf
import com.sun.tools.javac.util.List as JavacList

class MethodUtils(private val utils: JTCUtils) {

  inner class MethodSymbolWrapper(val sym: Symbol.MethodSymbol, val unknownTypes: List<String> = emptyList()) {

    override fun equals(other: Any?): Boolean {
      if (this === other) return true
      if (other !is MethodSymbolWrapper) return false
      // TODO use sameMethod instead of sameErasedMethod when we support generics
      return sameErasedMethod(sym, other.sym)
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
  private val types = Types.instance((utils.checker.processingEnvironment as JavacProcessingEnvironment).context)
  private val resolver = utils.resolver

  private fun erasure(sym: Symbol.MethodSymbol): Type = sym.erasure(types)

  fun methodNodeToMethodSymbol(env: Env<AttrContext>, node: TMethodNode, owner: Symbol.ClassSymbol): MethodSymbolWrapper {
    val unknownTypes = mutableListOf<String>()
    fun resolve(type: String): Type {
      val resolved = resolver.resolve(env, type)
      return if (resolved == null) {
        unknownTypes.add(type)
        symtab.unknownType
      } else resolved
    }

    val flags = Flags.PUBLIC.toLong()
    val name = names.fromString(node.name)
    val argtypes = JavacList.from(node.args.map { resolve(it.stringName()) })
    val restype = resolve(node.returnType.stringName())
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

  fun sameErasedMethod(a: Symbol.MethodSymbol, b: Symbol.MethodSymbol): Boolean {
    return a.name.toString() == b.name.toString() && utils.isSameType(erasure(a), erasure(b))
  }

  // We could use "typeUtils.isSameType" with the MethodType, but it does not compare thrown types
  private fun sameMethod(env: Env<AttrContext>, name: String, type: Type, node: TMethodNode): Boolean {
    // TODO deal with thrownTypes and typeArguments
    return name == node.name &&
      utils.isSameType(type.returnType, resolver.resolve(env, node.returnType.stringName())) &&
      utils.isSameTypes(type.parameterTypes, node.args.map { resolver.resolve(env, it.stringName()) }) // &&
    // TODO ignore exceptions while we do not support them in typestates
    // utils.isSameTypes(type.thrownTypes, listOf())
  }

  fun sameMethod(env: Env<AttrContext>, sym: Symbol.MethodSymbol, node: TMethodNode): Boolean {
    return sameMethod(env, sym.name.toString(), sym.type, node)
  }

  fun sameErasedMethod(env: Env<AttrContext>, sym: Symbol.MethodSymbol, node: TMethodNode): Boolean {
    return sameMethod(env, sym.name.toString(), erasure(sym), node)
  }

  companion object {
    fun returnsBoolean(method: Symbol.MethodSymbol): Boolean {
      return JTCUtils.isBoolean(method.returnType)
    }

    fun returnsEnum(method: Symbol.MethodSymbol): Boolean {
      return JTCUtils.isEnum(method.returnType)
    }
  }

}
