package org.checkerframework.checker.jtc.core

import com.sun.tools.javac.code.*
import com.sun.tools.javac.processing.JavacProcessingEnvironment
import org.checkerframework.checker.jtc.JavaTypestateChecker
import org.checkerframework.javacutil.ElementUtils
import org.checkerframework.javacutil.TypesUtils
import javax.lang.model.type.TypeKind
import javax.lang.model.type.TypeMirror

private var javaTypeUuid = 1L

// Given the fact that, in practise, there will be only one instance of the JavaTypesHierarchy,
// JavaType's can and will be compared by reference
class JavaType internal constructor(val original: Type, private val checker: JavaTypestateChecker) {
  val id = javaTypeUuid++
  internal val superTypes = mutableSetOf<JavaType>()

  fun isFinal() = original.isFinal || original.isPrimitiveOrVoid || original.kind == TypeKind.NULL
  fun isImmutable() = TypesUtils.isImmutableTypeInJdk(original)
  fun isEnum() = original.tsym.let { it is Symbol.ClassSymbol && it.isEnum }
  fun isJavaObject() = TypesUtils.isObject(original)
  fun isJavaEnum() = original.toString() == "java.lang.Enum<E>"

  fun getGraph() = checker.utils.classUtils.visitClassTypeMirror(original)
  fun hasProtocol() = checker.utils.classUtils.hasProtocol(original)

  fun isSubtype(other: JavaType): Boolean {
    return this == other || superTypes.any { it.isSubtype(other) }
  }

  fun qualifiedName(): String {
    val sym = original.tsym
    return if (sym is Symbol.ClassSymbol) sym.qualifiedName.toString() else original.toString()
  }

  fun getEnumLabels(): Pair<String, List<String>> {
    val type = original.tsym
    if (type is Symbol.ClassSymbol && type.isEnum) {
      return Pair(
        "${type.qualifiedName}",
        type.members().symbols.filter { it.isEnum && ElementUtils.isStatic(it) }.map { "${it.simpleName}" }
      )
    }
    error("JavaType.getEnumLabels should only be called on enum types")
  }

  override fun toString(): String {
    return original.toString()
  }
}

class JavaTypesHierarchy(private val checker: JavaTypestateChecker) {
  private val env = (checker.processingEnvironment as JavacProcessingEnvironment)
  private val types = Types.instance(env.context)
  private val symtab = Symtab.instance(env.context)
  private val typeUtils = env.typeUtils

  private fun isSameType(a: Type, b: Type): Boolean {
    if (a.tag == TypeTag.UNKNOWN) return b.tag == TypeTag.UNKNOWN
    if (b.tag == TypeTag.UNKNOWN) return a.tag == TypeTag.UNKNOWN
    // TODO isSameType for methods does not take thrown exceptions into account
    return typeUtils.isSameType(a, b) // && isSameTypes(a.thrownTypes, b.thrownTypes)
  }

  private inner class JavaTypeWrapper(type: Type) {
    val original = types.erasure(type)

    override fun equals(other: Any?): Boolean {
      return other is JavaTypeWrapper && isSameType(original, other.original)
    }

    override fun hashCode(): Int {
      return original.tag.hashCode()
    }
  }

  private val cache = mutableMapOf<JavaTypeWrapper, JavaType>()

  fun get(typeMirror: TypeMirror): JavaType {
    return get(typeMirror as Type)
  }

  fun get(type: Type): JavaType {
    val wrapper = JavaTypeWrapper(type)
    val curr = cache[wrapper]
    if (curr == null) {
      val javaType = JavaType(wrapper.original, checker)
      cache[wrapper] = javaType
      val clazz = javaType.original.tsym
      if (clazz is Symbol.ClassSymbol && !javaType.isJavaObject()) {
        // Add interfaces
        for (inter in clazz.interfaces) {
          javaType.superTypes.add(get(inter))
        }
        if (javaType.original.isInterface) {
          // If it is an interface, and extends no other interface, add java.lang.Object as superclass
          if (javaType.superTypes.isEmpty()) {
            javaType.superTypes.add(get(symtab.objectType))
          }
        } else {
          // Add superclass if it is not java.lang.Object or if no supertype was registered yet
          val superclass = get(clazz.superclass)
          if (javaType.superTypes.isEmpty() || !superclass.isJavaObject()) {
            javaType.superTypes.add(superclass)
          }
        }
      }
      return javaType
    }
    return curr
  }

  val BYTE = prim(symtab.byteType)
  val BOOLEAN = prim(symtab.booleanType)
  val CHAR = prim(symtab.charType)
  val DOUBLE = prim(symtab.doubleType)
  val FLOAT = prim(symtab.floatType)
  val INTEGER = prim(symtab.intType)
  val LONG = prim(symtab.longType)
  val SHORT = prim(symtab.shortType)

  val STRING = JTCSharedType(get(symtab.stringType))
  val ENUM = JTCSharedType(get(symtab.enumSym.asType()))

  fun getPrimitive(type: Type.JCPrimitiveType): JTCType {
    return when (type.tag) {
      TypeTag.BYTE -> BYTE
      TypeTag.CHAR -> CHAR
      TypeTag.SHORT -> SHORT
      TypeTag.INT -> INTEGER
      TypeTag.LONG -> LONG
      TypeTag.FLOAT -> FLOAT
      TypeTag.DOUBLE -> DOUBLE
      TypeTag.BOOLEAN -> BOOLEAN
      else -> error("Unexpected primitive tag ${type.tag}")
    }
  }

  private fun prim(javaType: Type): JTCPrimitiveType {
    return JTCPrimitiveType(get(javaType))
  }

  fun sameType(a: Type?, b: Type?): Boolean {
    if (a == null) return b == null
    if (b == null) return false
    return get(a) == get(b)
  }

  fun sameType(a: JavaType?, b: Type?): Boolean {
    if (a == null) return b == null
    if (b == null) return false
    return a == get(b)
  }

}

/*class TypeTable(val leastTypes: Set<JavaType>, val map: Map<JavaType, JTCType>, val knowsActualType: Boolean) {

  fun toUnknown(): TypeTable {

  }

  fun toBottom(): TypeTable {

  }

  fun union(other: TypeTable): TypeTable {

  }

  fun intersect(other: TypeTable): TypeTable {

  }

  fun toMoved(): TypeTable {

  }

  fun format(): String {
    return "[${leastTypes.joinToString(", ") { "($it, ${map[it]?.format()})" }}]"
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    return other is TypeTable && knowsActualType == other.knowsActualType && leastTypes == other.leastTypes && map == other.map
  }

  override fun hashCode(): Int {
    var result = leastTypes.hashCode()
    result = 31 * result + map.hashCode()
    result = 31 * result + knowsActualType.hashCode()
    return result
  }

  companion object {
    val UNKNOWN = TypeTable(emptySet(), emptyMap(), false)
  }

}*/
