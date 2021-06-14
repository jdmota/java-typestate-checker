package jatyc.assertions

import com.sun.source.tree.*
import com.sun.tools.javac.code.Symbol.VarSymbol
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.dataflow.cfg.node.*
import org.checkerframework.javacutil.ElementUtils
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.javacutil.TypesUtils
import javax.lang.model.element.Element
import javax.lang.model.element.ElementKind.*
import javax.lang.model.element.Modifier
import javax.lang.model.element.VariableElement
import javax.lang.model.type.TypeKind
import javax.lang.model.type.TypeMirror

// Adapted from https://github.com/typetools/checker-framework/blob/master/dataflow/src/main/java/org/checkerframework/dataflow/analysis/FlowExpressions.java

fun getReference(node: Node): Reference? {
  return when (node) {
    is FieldAccessNode -> {
      when (node.fieldName) {
        "this" -> {
          // For some reason, "className.this" is considered a field access.
          ThisReference(node.receiver.type)
        }
        "class" -> {
          // "className.class" is considered a field access. This makes sense,
          // since .class is similar to a field access which is the equivalent
          // of a call to getClass(). However for the purposes of dataflow
          // analysis, and value stores, this is the equivalent of a ClassNameNode.
          ClassName(node.receiver.type)
        }
        else -> {
          FieldAccess(
            if (node.isStatic) ClassName(node.receiver.type) else getReference(node.receiver)!!,
            node.type,
            node.element
          )
        }
      }
    }
    is ExplicitThisLiteralNode -> ThisReference(node.getType())
    is ThisLiteralNode -> ThisReference(node.getType())
    is SuperNode -> ThisReference(node.getType())
    is LocalVariableNode -> LocalVariable(node)
    is ClassNameNode -> ClassName(node.type)
    else -> null
  }
}

fun getReference(tree: Tree): Reference? {
  return when (tree) {
    is MemberSelectTree -> {
      val expressionType = TreeUtils.typeOf(tree.expression)
      if (TreeUtils.isClassLiteral(tree)) {
        return ClassName(expressionType)
      }
      val ele = TreeUtils.elementFromUse(tree)!!
      if (ElementUtils.isClassElement(ele)) {
        return ClassName(TreeUtils.typeOf(tree))
      }
      return when (ele.kind) {
        METHOD, CONSTRUCTOR -> getReference(tree.expression)
        ENUM_CONSTANT, FIELD -> {
          val fieldType = TreeUtils.typeOf(tree)
          val r = getReference(tree.expression)!!
          FieldAccess(r, fieldType, ele as VariableElement)
        }
        else -> null
      }
    }
    is IdentifierTree -> {
      val typeOfId = TreeUtils.typeOf(tree)
      if ((tree.name.contentEquals("this") || tree.name.contentEquals("super"))) {
        return ThisReference(typeOfId)
      }
      val ele = TreeUtils.elementFromUse(tree)!!
      if (ElementUtils.isClassElement(ele)) {
        return ClassName(ele.asType())
      }
      when (ele.kind) {
        LOCAL_VARIABLE, RESOURCE_VARIABLE, EXCEPTION_PARAMETER, PARAMETER -> LocalVariable(ele)
        FIELD -> {
          val enclosingType = ElementUtils.enclosingClass(ele)!!.asType()
          val fieldAccessExpression = if (ElementUtils.isStatic(ele)) {
            ClassName(enclosingType)
          } else {
            ThisReference(enclosingType)
          }
          return FieldAccess(fieldAccessExpression, typeOfId, ele as VariableElement)
        }
        else -> null
      }
    }
    else -> null
  }
}

fun createFieldAccess(tree: VariableTree, classTree: ClassTree): FieldAccess {
  val receiverType = TreeUtils.elementFromDeclaration(classTree).asType()
  val type = TreeUtils.elementFromDeclaration(tree).asType()
  val element = TreeUtils.elementFromTree(tree) as VariableElement
  return FieldAccess(ThisReference(receiverType), type, element)
}

fun createLocalVariable(tree: VariableTree): LocalVariable {
  return LocalVariable(LocalVariableNode(tree))
}

fun createParameterVariable(tree: VariableTree): ParameterVariable {
  return ParameterVariable(LocalVariableNode(tree))
}

sealed class Reference(val type: TypeMirror, val parent: Reference?) {
  val typeString get() = type.toString()

  abstract fun isThisField(): Boolean
  abstract fun withNewParent(parent: Reference): Reference

  override fun equals(other: Any?): Boolean {
    return other is Reference && parent == other.parent
  }

  override fun hashCode(): Int {
    return parent?.hashCode() ?: 0
  }

  override fun toString(): String {
    return if (parent == null) "" else "$parent."
  }

  fun replace(x: Reference, by: Reference): Reference {
    if (this == x) return by
    if (parent == null) return this
    val newReceiver = parent.replace(x, by)
    if (newReceiver === parent) return this
    return withNewParent(newReceiver)
  }

  fun hasPrefix(prefix: Reference): Boolean {
    if (this == prefix) return true
    if (parent == null) return false
    return parent.hasPrefix(prefix)
  }

  fun withCtx(ctx: OuterContextRef): Reference {
    return if (parent == null) {
      withNewParent(ctx)
    } else {
      withNewParent(parent.withCtx(ctx))
    }
  }

  fun getSimpleRoot(): Reference {
    return if (this is FieldAccess) {
      receiver.getSimpleRoot()
    } else {
      this
    }
  }

  fun isPrimitive(): Boolean {
    return TypesUtils.isPrimitive(type) || type.kind == TypeKind.VOID
  }
}

class FieldAccess(val receiver: Reference, type: TypeMirror, val field: VariableElement) : Reference(type, receiver) {

  constructor(receiver: Reference, field: VariableElement) : this(receiver, ElementUtils.getType(field), field)

  val isFinal get() = ElementUtils.isFinal(field)
  val isStatic get() = ElementUtils.isStatic(field)
  val isNonPrivate = !field.modifiers.contains(Modifier.PRIVATE)

  val fieldName get() = field.simpleName.toString()

  override fun isThisField(): Boolean {
    return if (receiver is ThisReference) receiver.parent == null else receiver.isThisField()
  }

  override fun equals(other: Any?): Boolean {
    return other is FieldAccess && other.field == field && other.receiver == receiver
  }

  override fun hashCode(): Int {
    var result = receiver.hashCode()
    result = 31 * result + field.hashCode()
    return result
  }

  override fun toString(): String {
    return "$receiver.$field"
  }

  override fun withNewParent(parent: Reference): Reference {
    return FieldAccess(parent, type, field)
  }
}

class ThisReference(parent: Reference?, type: TypeMirror) : Reference(type, parent) {

  constructor(type: TypeMirror) : this(null, type)

  override fun isThisField(): Boolean {
    return false
  }

  override fun equals(other: Any?): Boolean {
    return other is ThisReference && super.equals(other)
  }

  override fun hashCode(): Int {
    return 31 * super.hashCode() + 1
  }

  override fun toString(): String {
    return super.toString() + "this"
  }

  override fun withNewParent(parent: Reference): Reference {
    return ThisReference(parent, type)
  }
}

class ClassName(parent: Reference?, type: TypeMirror) : Reference(type, parent) {

  constructor(type: TypeMirror) : this(null, type)

  override fun isThisField(): Boolean {
    return false
  }

  override fun equals(other: Any?): Boolean {
    return other is ClassName && other.typeString == typeString && super.equals(other)
  }

  override fun hashCode(): Int {
    return 31 * super.hashCode() + typeString.hashCode()
  }

  override fun toString(): String {
    return super.toString() + "$typeString.class"
  }

  override fun withNewParent(parent: Reference): Reference {
    return ClassName(parent, type)
  }
}

class LocalVariable(parent: Reference?, type: TypeMirror, val element: VarSymbol) : Reference(type, parent) {

  constructor(type: TypeMirror, element: VarSymbol) : this(null, type, element)
  constructor(node: LocalVariableNode) : this(node.type, node.element as VarSymbol)
  constructor(elem: Element) : this(ElementUtils.getType(elem), elem as VarSymbol)

  val elementName = element.name.toString()
  val ownerName = element.owner.toString()

  override fun isThisField(): Boolean {
    return false
  }

  override fun equals(other: Any?): Boolean {
    if (other !is LocalVariable) return false
    // The code below isn't just return vs.equals(vsother) because an element might be
    // different between subcheckers. The owner of a lambda parameter is the enclosing
    // method, so a local variable and a lambda parameter might have the same name and the
    // same owner. pos is used to differentiate this case.
    return element.pos == other.element.pos && other.elementName == elementName && other.ownerName == ownerName && super.equals(other)
  }

  override fun hashCode(): Int {
    var result = super.hashCode()
    result = 31 * result + elementName.hashCode()
    result = 31 * result + ownerName.hashCode()
    return result
  }

  override fun toString(): String {
    return super.toString() + elementName
  }

  override fun withNewParent(parent: Reference): Reference {
    return LocalVariable(parent, type, element)
  }
}

class ParameterVariable(parent: Reference?, type: TypeMirror, val element: VarSymbol) : Reference(type, parent) {

  constructor(type: TypeMirror, element: VarSymbol) : this(null, type, element)
  constructor(node: LocalVariableNode) : this(node.type, node.element as VarSymbol)
  constructor(elem: Element) : this(ElementUtils.getType(elem), elem as VarSymbol)

  val elementName = element.name.toString()
  val ownerName = element.owner.toString()

  fun toLocalVariable() = LocalVariable(parent, type, element)

  override fun isThisField(): Boolean {
    return false
  }

  override fun equals(other: Any?): Boolean {
    if (other !is ParameterVariable) return false
    // The code below isn't just return vs.equals(vsother) because an element might be
    // different between subcheckers. The owner of a lambda parameter is the enclosing
    // method, so a local variable and a lambda parameter might have the same name and the
    // same owner. pos is used to differentiate this case.
    return element.pos == other.element.pos && other.elementName == elementName && other.ownerName == ownerName && super.equals(other)
  }

  override fun hashCode(): Int {
    var result = super.hashCode()
    result = 31 * result + elementName.hashCode()
    result = 31 * result + ownerName.hashCode()
    return result
  }

  override fun toString(): String {
    return super.toString() + "param($elementName)"
  }

  override fun withNewParent(parent: Reference): Reference {
    return ParameterVariable(parent, type, element)
  }
}

class ReturnSpecialVar(parent: Reference?, type: TypeMirror) : Reference(type, parent) {

  constructor(type: TypeMirror) : this(null, type)

  override fun isThisField(): Boolean {
    return false
  }

  override fun equals(other: Any?): Boolean {
    return other is ReturnSpecialVar && super.equals(other)
  }

  override fun hashCode(): Int {
    return 31 * super.hashCode() + 2
  }

  override fun toString(): String {
    return super.toString() + "#ret"
  }

  override fun withNewParent(parent: Reference): Reference {
    return ReturnSpecialVar(parent, type)
  }
}

// The "pos" distinguishes between different assignments
class OldSpecialVar(parent: Reference?, val reference: Reference, val pos: Int) : Reference(reference.type, parent) {

  constructor(reference: Reference, pos: Int) : this(null, reference, pos)

  override fun isThisField(): Boolean {
    return false
  }

  override fun equals(other: Any?): Boolean {
    return other is OldSpecialVar && reference == other.reference && pos == other.pos && super.equals(other)
  }

  override fun hashCode(): Int {
    var result = super.hashCode()
    result = 31 * result + reference.hashCode()
    result = 31 * result + pos
    return result
  }

  override fun toString(): String {
    return super.toString() + "old($reference)[$pos]"
  }

  override fun withNewParent(parent: Reference): Reference {
    return OldSpecialVar(parent, reference, pos)
  }
}

class NodeRef(parent: Reference?, val node: Node) : Reference(node.type, parent) {

  constructor(node: Node) : this(null, node)

  override fun isThisField(): Boolean {
    return false
  }

  override fun equals(other: Any?): Boolean {
    return other is NodeRef && node === other.node && super.equals(other)
  }

  override fun hashCode(): Int {
    return 31 * super.hashCode() + System.identityHashCode(node)
  }

  override fun toString(): String {
    return super.toString() + "node($node)[${(node.tree as? JCTree)?.pos}]"
  }

  override fun withNewParent(parent: Reference): Reference {
    return NodeRef(parent, node)
  }
}

class UnknownRef(type: TypeMirror) : Reference(type, null) {

  override fun isThisField(): Boolean {
    return false
  }

  override fun equals(other: Any?): Boolean {
    return other is UnknownRef && super.equals(other)
  }

  override fun hashCode(): Int {
    return 31 * super.hashCode()
  }

  override fun toString(): String {
    return super.toString() + "unknown"
  }

  override fun withNewParent(parent: Reference): Reference {
    return UnknownRef(type)
  }
}

class OuterContextRef(parent: Reference?, val tree: Tree, type: TypeMirror) : Reference(type, parent) {

  override fun isThisField(): Boolean {
    return false
  }

  override fun equals(other: Any?): Boolean {
    return other is OuterContextRef && tree === other.tree && super.equals(other)
  }

  override fun hashCode(): Int {
    return 31 * super.hashCode() + System.identityHashCode(tree)
  }

  private fun treeName() = when (tree) {
    is MethodTree -> tree.name.toString()
    is LambdaExpressionTree -> "lambda"
    else -> "unknown"
  }

  override fun toString(): String {
    return super.toString() + "#outer_${treeName()}"
  }

  override fun withNewParent(parent: Reference): Reference {
    return OuterContextRef(parent, tree, type)
  }
}
