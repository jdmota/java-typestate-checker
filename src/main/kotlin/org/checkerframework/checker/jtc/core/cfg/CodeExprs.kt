package org.checkerframework.checker.jtc.core.cfg

import com.sun.source.tree.CompilationUnitTree
import javax.lang.model.type.TypeMirror
import com.sun.source.tree.Tree
import org.checkerframework.checker.jtc.core.JTCType
import org.checkerframework.checker.jtc.core.JavaType
import org.checkerframework.checker.jtc.core.Reference
import org.checkerframework.dataflow.cfg.node.*
import org.checkerframework.checker.jtc.typestate.graph.Graph

sealed class AdaptedThing {
  var cfNode: Node? = null
  var cfTree: Tree? = null
  var cfType: TypeMirror? = null
  var cfRoot: CompilationUnitTree? = null
}

fun <T : AdaptedThing> T.set(node: Node?): T {
  if (node != null) {
    cfNode = node
    if (cfTree == null) {
      cfTree = node.tree
    }
    if (cfType == null) {
      cfType = node.type
    }
  }
  return this
}

fun <T : AdaptedThing> T.set(tree: Tree?): T {
  if (tree != null) {
    cfTree = tree
  }
  // cfType = TreeUtils.typeOf(t)
  return this
}

fun <T : AdaptedThing> T.set(type: TypeMirror?): T {
  if (type != null) {
    cfType = type
  }
  return this
}

fun <T : AdaptedThing> T.set(root: CompilationUnitTree): T {
  cfRoot = root
  return this
}

/** Left Hand Side */

sealed class LeftHS : AdaptedThing() {
  abstract fun toCode(): CodeExpr
}

class SelectLHS(val obj: CodeExpr, val id: String, val uuid: Long) : LeftHS() {
  override fun toCode(): CodeExpr {
    return Select(obj, id, uuid)
  }

  override fun equals(other: Any?): Boolean {
    return other is SelectLHS && obj == other.obj && id == other.id && uuid == other.uuid
  }

  override fun hashCode(): Int {
    var result = obj.hashCode()
    result = 31 * result + id.hashCode()
    result = 31 * result + uuid.hashCode()
    return result
  }

  override fun toString() = "$obj.$id[${uuid}]"
}

class IdLHS(val name: String, val uuid: Long) : LeftHS() {
  override fun toCode(): CodeExpr {
    return Id(name, uuid)
  }

  override fun equals(other: Any?): Boolean {
    return other is IdLHS && name == other.name && uuid == other.uuid
  }

  override fun hashCode(): Int {
    var result = name.hashCode()
    result = 31 * result + uuid.hashCode()
    return result
  }

  override fun toString() = "$name[$uuid]"
}

/** Code expressions */

sealed class CodeExpr : AdaptedThing() {
  abstract fun format(indent: String): String
  override fun toString() = format("")
}

class Select(val expr: CodeExpr, val id: String, val uuid: Long) : CodeExpr() {
  override fun format(indent: String): String {
    return "${expr.format(indent)}.$id"
  }

  override fun toString(): String {
    return "$expr.$id[$uuid]"
  }
}

class Id(val name: String, val uuid: Long) : CodeExpr() {
  override fun format(indent: String): String {
    return "$indent$name"
  }

  override fun toString(): String {
    return "$name[$uuid]"
  }
}

class Assign(val left: LeftHS, val right: CodeExpr) : CodeExpr() {
  override fun format(indent: String): String {
    return "$left = $right"
  }
}

class ParamAssign(val idx: Int, val expr: CodeExpr) : CodeExpr() {
  lateinit var call: MethodCall
  override fun format(indent: String): String {
    return "param$idx = $expr"
  }
}

class Return(val expr: CodeExpr?, val type: JTCType) : CodeExpr() {
  override fun format(indent: String): String {
    return "${indent}return ${expr?.format("")}"
  }
}

class NewObj(val type: JTCType, val javaType: JavaType) : CodeExpr() {
  override fun format(indent: String): String {
    return "${indent}new $javaType"
  }
}

class NewArrayWithValues(val type: JTCType, val javaType: JavaType, val componentType: JTCType, val componentJavaType: JavaType, val initializers: List<CodeExpr>) : CodeExpr() {
  override fun format(indent: String): String {
    return "${indent}new $javaType {${initializers.joinToString(", ") { it.format("") }}"
  }
}

class MethodCall(val methodExpr: FuncInterface, val parameters: List<ParamAssign>, val isSuperCall: Boolean) : CodeExpr() {
  init {
    if (methodExpr.parameters.size != parameters.size) {
      error("Arguments and parameters have different sizes: ${methodExpr.parameters.size} and ${parameters.size}")
    }

    for (param in parameters) {
      param.call = this
    }
  }

  override fun format(indent: String): String {
    val func = if (methodExpr.name == null) methodExpr.format(indent) else (indent + methodExpr.name)
    return func + "(${parameters.joinToString(", ") { it.expr.format("") }})"
  }
}

class FuncParam(val id: IdLHS, val requires: JTCType, val ensures: JTCType, val isThis: Boolean) : AdaptedThing() {
  override fun toString(): String {
    return "Param{$id, ${requires.format()}, ${ensures.format()}, isThis=$isThis}"
  }
}

class FuncDeclaration(
  name: String?,
  parameters: List<FuncParam>,
  val body: SimpleCFG,
  returnType: JTCType,
  isPublic: Boolean,
  isAnytime: Boolean,
  isPure: Boolean,
  var clazz: ClassDecl? = null
) : FuncInterface(name, parameters, returnType, isPublic, isAnytime, isPure) {
  override fun format(indent: String): String {
    return "$indent(fun ${name ?: "anonymous"}(...) -> ...)" // ${parameters.joinToString(", ")}
  }
}

open class FuncInterface(
  val name: String?,
  val parameters: List<FuncParam>,
  val returnType: JTCType,
  val isPublic: Boolean,
  val isAnytime: Boolean,
  val isPure: Boolean
) : CodeExpr() {
  val isConstructor = name == "<init>"
  override fun format(indent: String): String {
    return "$indent(fun_i ${name ?: "anonymous"}(...) -> ...)" // ${parameters.joinToString(", ")}
  }
}

class VarDeclaration(val id: IdLHS, val type: JTCType) : CodeExpr() {
  override fun format(indent: String): String {
    return indent + "var $id"
  }
}

class FieldDeclaration(val id: IdLHS, val type: JTCType, val isPrivate: Boolean, val isProtected: Boolean, val isPublic: Boolean) : AdaptedThing() {
  override fun toString(): String {
    return "field $id"
  }
}

class ClassDecl(
  val name: String,
  val fields: List<FieldDeclaration>,
  val methods: List<FuncDeclaration>, // == publicMethods + nonPublicMethods
  val publicMethods: List<FuncDeclaration>,
  val nonPublicMethods: List<FuncDeclaration>,
  val classes: List<ClassDeclAndCompanion>,
  val extends: List<String>,
  val overrides: Map<FuncDeclaration, List<FuncInterface>>,
  val thisRef: Reference?, // null for static classes
  val graph: Graph?
) : CodeExpr() {
  fun allPublicMethods(classes: Map<String, ClassDeclAndCompanion>): Sequence<FuncDeclaration> = sequence {
    for (method in publicMethods) {
      if (!method.isConstructor) {
        yield(method)
      }
    }
    for (baseName in extends) {
      val base = classes[baseName]
      if (base != null) yieldAll(base.nonStatic.allPublicMethods(classes))
    }
  }

  fun protocolMethods(classes: Map<String, ClassDeclAndCompanion>): Sequence<FuncDeclaration> = sequence {
    for (method in publicMethods) {
      if (!method.isAnytime && !method.isConstructor) {
        yield(method)
      }
    }
    for (baseName in extends) {
      val base = classes[baseName]
      if (base != null) yieldAll(base.nonStatic.protocolMethods(classes))
    }
  }

  fun allFields(classes: Map<String, ClassDeclAndCompanion>): Sequence<FieldDeclaration> = sequence {
    for (field in fields) {
      yield(field)
    }
    for (baseName in extends) {
      val base = classes[baseName]
      if (base != null) yieldAll(base.nonStatic.allFields(classes))
    }
  }

  fun allFieldsExceptOurs(classes: Map<String, ClassDeclAndCompanion>): Sequence<FieldDeclaration> = sequence {
    for (baseName in extends) {
      val base = classes[baseName]
      if (base != null) yieldAll(base.nonStatic.allFields(classes))
    }
  }

  fun constructors(): Sequence<FuncDeclaration> = sequence {
    for (method in methods) {
      if (method.isConstructor) {
        yield(method)
      }
    }
  }

  fun nonConstructors(): Sequence<FuncDeclaration> = sequence {
    for (method in methods) {
      if (!method.isConstructor) {
        yield(method)
      }
    }
  }

  override fun format(indent: String): String {
    return "${indent}class $name {"
    /*val lines = mutableListOf<String>()
    lines.add("${indent}class $name {")
    for (f in fields) {
      lines.add("$indent  $f")
    }
    for (m in publicMethods) {
      lines.add("$indent public $m")
    }
    for (m in nonPublicMethods) {
      lines.add("$indent  $m")
    }
    for (clazz in classes) {
      lines.add(clazz.format("$indent  "))
    }
    lines.add("$indent}")
    return lines.joinToString("\n")*/
  }
}

class ClassDeclAndCompanion(val nonStatic: ClassDecl, val static: ClassDecl) : CodeExpr() {
  override fun format(indent: String): String {
    return "class ${nonStatic.name} + companion"
  }
}

// For classes and packages
class SymbolResolveExpr(val type: JTCType, val javaType: JavaType) : CodeExpr() {
  val qualifiedName = javaType.qualifiedName()
  override fun format(indent: String): String {
    return "$indent$qualifiedName"
  }
}

enum class BinaryOP {
  BitwiseAnd,
  BitwiseOr,
  BitwiseXor,
  And,
  Or,
  Equal,
  FloatDivision,
  FloatRemainder,
  GreaterThan,
  GreaterThanOrEqual,
  IntDivision,
  IntRemainder,
  LeftShift,
  LessThan,
  LessThanOrEqual,
  NotEqual,
  Add,
  Mult,
  Sub,
  SignedRightShift,
  StringConcat,
  UnsignedRightShift,
  Is
}

class BinaryExpr(val left: CodeExpr, val right: CodeExpr, val operator: BinaryOP) : CodeExpr() {
  override fun format(indent: String): String {
    return "$indent$left $operator $right"
  }
}

enum class UnaryOP {
  BitwiseComplement,
  Not,
  Minus,
  Plus,
  Widening,
  Narrowing
}

class NullCheck(val expr: CodeExpr, val message: String) : CodeExpr() {
  override fun format(indent: String): String {
    return "${indent}nullCheck $expr"
  }
}

class UnaryExpr(val expr: CodeExpr, val operator: UnaryOP) : CodeExpr() {
  override fun format(indent: String): String {
    return "$indent$operator $expr"
  }
}

class TernaryExpr(val condition: CodeExpr, val thenExpr: CodeExpr, val elseExpr: CodeExpr) : CodeExpr() {
  override fun format(indent: String): String {
    return "$indent$condition ? $thenExpr : $elseExpr"
  }
}

class CaseExpr(val caseOp: CodeExpr, val switchOp: CodeExpr) : CodeExpr() {
  override fun format(indent: String): String {
    return indent + "case $caseOp"
  }
}

class ThrowExpr(val expr: CodeExpr?) : CodeExpr() {
  override fun format(indent: String): String {
    return indent + "throw $expr"
  }
}

class CastExpr(val expr: CodeExpr, val type: JTCType, val javaType: JavaType) : CodeExpr() {
  override fun format(indent: String): String {
    return "$indent($javaType) ${expr.format("")}"
  }
}

class SynchronizedExprStart(val expr: CodeExpr) : CodeExpr() {
  override fun format(indent: String): String {
    return indent + "sync_start"
  }
}

class SynchronizedExprEnd(val expr: CodeExpr) : CodeExpr() {
  override fun format(indent: String): String {
    return indent + "sync_end"
  }
}

class NoOPExpr(val message: String) : CodeExpr() {
  override fun format(indent: String): String {
    return indent + "debug($message)"
  }
}

sealed class Literal : CodeExpr()
class BooleanLiteral(val value: Boolean) : Literal() {
  override fun format(indent: String) = indent + value.toString()
}

class CharLiteral(val value: Char) : Literal() {
  override fun format(indent: String) = indent + value.toString()
}

class DoubleLiteral(val value: Double) : Literal() {
  override fun format(indent: String) = indent + value.toString()
}

class FloatLiteral(val value: Float) : Literal() {
  override fun format(indent: String) = indent + value.toString()
}

class IntegerLiteral(val value: Int) : Literal() {
  override fun format(indent: String) = indent + value.toString()
}

class LongLiteral(val value: Long) : Literal() {
  override fun format(indent: String) = indent + value.toString()
}

class NullLiteral : Literal() {
  override fun format(indent: String) = indent + "null"
}

class ShortLiteral(val value: Short) : Literal() {
  override fun format(indent: String) = indent + value.toString()
}

class StringLiteral(val value: String) : Literal() {
  override fun format(indent: String) = indent + "\"$value\""
}
