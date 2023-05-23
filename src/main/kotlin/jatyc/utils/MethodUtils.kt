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
      // TODO use erasure while we do not support generics
      return sym.name.toString() == other.sym.name.toString() && utils.isSameType(erasure(sym), erasure(other.sym))
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

  companion object {
    fun returnsBoolean(method: Symbol.MethodSymbol): Boolean {
      return JTCUtils.isBoolean(method.returnType)
    }

    fun returnsEnum(method: Symbol.MethodSymbol): Boolean {
      return JTCUtils.isEnum(method.returnType)
    }
  }

}
