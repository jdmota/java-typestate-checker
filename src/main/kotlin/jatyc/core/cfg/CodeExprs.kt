package jatyc.core.cfg

import com.sun.source.tree.CompilationUnitTree
import javax.lang.model.type.TypeMirror
import com.sun.source.tree.Tree
import jatyc.JavaTypestateChecker
import jatyc.core.*
import org.checkerframework.dataflow.cfg.node.*
import jatyc.typestate.graph.Graph

sealed class AdaptedThing {
  var cfTree: Tree? = null
  var cfType: TypeMirror? = null
  var cfRoot: CompilationUnitTree? = null
  var suppressWarnings: Boolean = false
  var javaType2: JavaType? = null
}

fun <T : AdaptedThing> T.set(node: Node, hierarchy: JavaTypesHierarchy): T {
  set(node.tree)
  set(node.type, hierarchy)
  return this
}

fun <T : AdaptedThing> T.set(tree: Tree?): T {
  if (tree != null) {
    cfTree = tree
  }
  return this
}

fun <T : AdaptedThing> T.set(type: TypeMirror?, hierarchy: JavaTypesHierarchy): T {
  if (type != null) {
    cfType = type
    if (javaType2 == null) {
      javaType2 = hierarchy.get(type)
    }
  }
  return this
}

fun <T : AdaptedThing> T.set(javaType: JavaType): T {
  cfType = javaType.original
  javaType2 = javaType
  return this
}

fun <T : AdaptedThing> T.set(root: CompilationUnitTree): T {
  cfRoot = root
  return this
}

fun <T : AdaptedThing> T.set(checker: JavaTypestateChecker): T {
  if (cfTree != null) {
    suppressWarnings = checker.shouldSuppressWarnings(cfTree, "some error")
  }
  return this
}

/** Left Hand Side */
sealed class LeftHS(val javaType: JavaType) : AdaptedThing() {
  abstract fun format(indent: String): String
  abstract fun toCode(): CodeExpr

  fun format() = format("")
}

class SelectLHS(val obj: CodeExpr, val id: String, val uuid: Long, javaType: JavaType) : LeftHS(javaType) {
  override fun toCode(): CodeExpr {
    return Select(obj, id, uuid, javaType)
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

  override fun format(indent: String): String {
    return "${obj.format(indent)}.$id"
  }

  override fun toString() = "$obj.$id[${uuid}]"
}

class IdLHS(val name: String, val uuid: Long, javaType: JavaType) : LeftHS(javaType) {
  override fun toCode(): CodeExpr {
    return Id(name, uuid, javaType)
  }

  override fun equals(other: Any?): Boolean {
    return other is IdLHS && name == other.name && uuid == other.uuid
  }

  override fun hashCode(): Int {
    var result = name.hashCode()
    result = 31 * result + uuid.hashCode()
    return result
  }

  override fun format(indent: String): String {
    return indent + name
  }

  override fun toString() = "$name[$uuid]"
}

/** Code expressions */
sealed class CodeExpr : AdaptedThing() {
  abstract fun format(indent: String): String
  override fun toString() = format("")

  fun format() = format("")
}

class Select(val expr: CodeExpr, val id: String, val uuid: Long, val javaType: JavaType) : CodeExpr() {
  init {
    javaType2 = javaType
  }

  override fun format(indent: String): String {
    return "${expr.format(indent)}.$id"
  }

  override fun toString(): String {
    return "$expr.$id[$uuid]"
  }
}

class Id(val name: String, val uuid: Long, val javaType: JavaType) : CodeExpr() {
  init {
    javaType2 = javaType
  }

  override fun format(indent: String): String {
    return "$indent$name"
  }

  override fun toString(): String {
    return "$name[$uuid]"
  }
}

class Assign(val left: LeftHS, val right: CodeExpr, val type: JTCType) : CodeExpr() {
  init {
    javaType2 = right.javaType2
  }

  override fun format(indent: String): String {
    return "$left = $right"
  }
}

class ParamAssign(val idx: Int, val expr: CodeExpr) : CodeExpr() {
  init {
    javaType2 = expr.javaType2
  }

  lateinit var call: MethodCall

  override fun format(indent: String): String {
    return "param$idx = $expr (the call: $call)"
  }
}

class Return(val expr: CodeExpr?, val type: JTCType, val javaType: JavaType) : CodeExpr() {
  override fun format(indent: String): String {
    return "${indent}return ${expr?.format("")}"
  }
}

class NewObj(val type: JTCType, val javaType: JavaType) : CodeExpr() {
  init {
    javaType2 = javaType
  }

  override fun format(indent: String): String {
    return "${indent}new $javaType"
  }
}

class NewArrayWithDimensions(val javaType: JavaType, val componentJavaType: JavaType, val dimensions: List<CodeExpr>) : CodeExpr() {
  init {
    javaType2 = javaType
  }

  override fun format(indent: String): String {
    return "${indent}new $javaType [${dimensions.joinToString(", ") { it.format("") }}]"
  }
}

class NewArrayWithValues(val javaType: JavaType, val componentJavaType: JavaType, val initializers: List<CodeExpr>) : CodeExpr() {
  init {
    javaType2 = javaType
  }

  override fun format(indent: String): String {
    return "${indent}new $javaType {${initializers.joinToString(", ") { it.format("") }}}"
  }
}

class ArrayAccess(val array: CodeExpr, val idx: CodeExpr, val arrayType: JavaType) : CodeExpr() {
  override fun format(indent: String): String {
    return "${array.format(indent)}[$idx]"
  }
}

class ArraySet(val left: ArrayAccess, val assignee: CodeExpr, val valueType: JavaType) : CodeExpr() {
  init {
    javaType2 = assignee.javaType2
  }

  override fun format(indent: String): String {
    return "${left.format(indent)} = ${assignee.format("")}"
  }
}

class MethodCall(val methodExpr: FuncInterface, val parameters: List<ParamAssign>, val isSuperCall: Boolean) : CodeExpr() {
  init {
    if (methodExpr.parameters.size != parameters.size) {
      error("Arguments and parameters have different sizes: ${methodExpr.parameters.size} and ${parameters.size}")
    }

    javaType2 = methodExpr.returnJavaType

    for (param in parameters) {
      param.call = this
    }
  }

  override fun format(indent: String): String {
    val func = if (methodExpr.name == null) methodExpr.format(indent) else (indent + methodExpr.name)
    return func + "(${parameters.joinToString(", ") { it.expr.format("") }})"
  }
}

class FuncParam(val id: IdLHS, val requires: JTCType, val ensures: JTCType, val isThis: Boolean, val hasEnsures: Boolean) : AdaptedThing() {
  override fun toString(): String {
    return "Param{$id, ${requires.format()}, ${ensures.format()}, isThis=$isThis, hasEnsures=$hasEnsures}"
  }
}

class FuncDeclaration(
  name: String?,
  parameters: List<FuncParam>,
  val body: SimpleCFG,
  returnType: JTCType,
  returnJavaType: JavaType,
  isPublic: Boolean,
  isAnytime: Boolean,
  isPure: Boolean,
  isAbstract: Boolean,
  var clazz: ClassDecl? = null
) : FuncInterface(name, parameters, returnType, returnJavaType, isPublic, isAnytime, isPure, isAbstract) {
  fun potentiallyModifiedFields(): Sequence<SelectReference>? {
    val info = body.detailedInfo
    return if (info.innerCalls.any { !it.methodExpr.isPure }) {
      null
    } else {
      info.potentiallyModified.asSequence()
    }
  }

  override fun format(indent: String): String {
    return "$indent(fun ${name ?: "anonymous"}(...) -> ...)" // ${parameters.joinToString(", ")}
  }
}

open class FuncInterface(
  val name: String?,
  val parameters: List<FuncParam>,
  val returnType: JTCType,
  val returnJavaType: JavaType,
  val isPublic: Boolean,
  val isAnytime: Boolean,
  val isPure: Boolean,
  val isAbstract: Boolean
) : CodeExpr() {
  val isConstructor = name == "<init>"
  override fun format(indent: String): String {
    return "$indent(fun_i ${name ?: "anonymous"}(...) -> ...)" // ${parameters.joinToString(", ")}
  }
}

class VarDeclaration(val id: IdLHS, val javaType: JavaType, val type: JTCType) : CodeExpr() {
  override fun format(indent: String): String {
    return indent + "var $id"
  }
}

class FieldDeclaration(val id: IdLHS, val javaType: JavaType, val type: JTCType, val isPrivate: Boolean, val isProtected: Boolean, val isPublic: Boolean) : AdaptedThing() {
  override fun toString(): String {
    return "field $id"
  }
}

class ClassDecl(
  val name: String,
  val fields: Map<String, FieldDeclaration>,
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
    for (base in resolveExtends(classes)) {
      yieldAll(base.nonStatic.allPublicMethods(classes))
    }
  }

  fun protocolMethods(classes: Map<String, ClassDeclAndCompanion>): Sequence<FuncDeclaration> = sequence {
    for (method in publicMethods) {
      if (!method.isAnytime && !method.isConstructor) {
        yield(method)
      }
    }
    for (base in resolveExtends(classes)) {
      yieldAll(base.nonStatic.protocolMethods(classes))
    }
  }

  fun allFields(classes: Map<String, ClassDeclAndCompanion>): Sequence<FieldDeclaration> = sequence {
    yieldAll(fields.values)
    yieldAll(superFields(classes))
  }

  fun superFields(classes: Map<String, ClassDeclAndCompanion>): Sequence<FieldDeclaration> = sequence {
    for (base in resolveExtends(classes)) {
      yieldAll(base.nonStatic.allFields(classes))
    }
  }

  fun superMethods(classes: Map<String, ClassDeclAndCompanion>): Sequence<FuncDeclaration> = sequence {
    for (base in resolveExtends(classes)) {
      yieldAll(base.nonStatic.methods)
    }
  }

  fun resolveExtends(classes: Map<String, ClassDeclAndCompanion>) = sequence {
    for (name in extends) {
      val base = classes[name]
      if (base != null) yield(base)
    }
  }

  fun resolveField(classes: Map<String, ClassDeclAndCompanion>, name: String, uuid: Long): FieldDeclaration? {
    val f = fields[name]
    if (f != null && f.id.uuid == uuid) return f
    for (base in resolveExtends(classes)) {
      val f = base.nonStatic.resolveField(classes, name, uuid)
      if (f != null) return f
    }
    return null
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
  Narrowing,
  ToString
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

class CaseExpr(val caseOps: List<CodeExpr>, val switchOp: CodeExpr) : CodeExpr() {
  override fun format(indent: String): String {
    return indent + "case $caseOps"
  }
}

class ThrowExpr(val expr: CodeExpr?) : CodeExpr() {
  override fun format(indent: String): String {
    return indent + "throw $expr"
  }
}

class CastExpr(val expr: CodeExpr, val type: JTCType, val javaType: JavaType, val upcast: Boolean) : CodeExpr() {
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
