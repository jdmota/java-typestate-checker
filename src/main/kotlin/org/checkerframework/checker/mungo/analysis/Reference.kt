package org.checkerframework.checker.mungo.analysis

import com.sun.source.tree.*
import com.sun.tools.javac.code.Symbol.VarSymbol
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.dataflow.cfg.node.*
import org.checkerframework.javacutil.ElementUtils
import org.checkerframework.javacutil.TreeUtils
import javax.lang.model.element.Element
import javax.lang.model.element.ElementKind.*
import javax.lang.model.element.Modifier
import javax.lang.model.element.VariableElement
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
    is ReturnNode -> ReturnSpecialVar(node.type)
    is VariableDeclarationNode -> getReference(LocalVariableNode(node.tree))
    is AssignmentNode -> OldSpecialVar(getReference(node.target)!!, (node.tree as JCTree).pos)
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

sealed class Reference(val type: TypeMirror) {
  abstract fun isThisField(): Boolean
}

fun createFieldAccess(tree: VariableTree, classTree: ClassTree): FieldAccess {
  val receiverType = TreeUtils.elementFromDeclaration(classTree).asType()
  val type = TreeUtils.elementFromDeclaration(tree).asType()
  val element = TreeUtils.elementFromTree(tree) as VariableElement
  return FieldAccess(ThisReference(receiverType), type, element)
}

fun createFieldAccess(receiver: Reference, tree: VariableTree): FieldAccess {
  val type = TreeUtils.elementFromDeclaration(tree).asType()
  val element = TreeUtils.elementFromTree(tree) as VariableElement
  return FieldAccess(receiver, type, element)
}

fun createLocalVariable(tree: VariableTree): LocalVariable {
  return LocalVariable(LocalVariableNode(tree))
}

class FieldAccess(val receiver: Reference, type: TypeMirror, val field: VariableElement) : Reference(type) {

  constructor(receiver: Reference, field: VariableElement) : this(receiver, ElementUtils.getType(field), field)

  val isFinal get() = ElementUtils.isFinal(field)
  val isStatic get() = ElementUtils.isStatic(field)
  val isNonPrivate = !field.modifiers.contains(Modifier.PRIVATE)

  override fun isThisField(): Boolean {
    return if (receiver is ThisReference) true else receiver.isThisField()
  }

  override fun equals(other: Any?): Boolean {
    if (other !is FieldAccess) return false
    return other.field == field && other.receiver == receiver
  }

  override fun hashCode(): Int {
    var result = receiver.hashCode()
    result = 31 * result + field.hashCode()
    return result
  }

  override fun toString(): String {
    return "$receiver.$field"
  }
}

class ThisReference(type: TypeMirror) : Reference(type) {
  override fun isThisField(): Boolean {
    return false
  }

  override fun equals(other: Any?): Boolean {
    return other is ThisReference
  }

  override fun hashCode(): Int {
    return 0
  }

  override fun toString(): String {
    return "this"
  }
}

class ClassName(type: TypeMirror) : Reference(type) {
  val typeString = type.toString()

  override fun isThisField(): Boolean {
    return false
  }

  override fun equals(other: Any?): Boolean {
    if (other !is ClassName) return false
    return other.typeString == typeString
  }

  override fun hashCode(): Int {
    return typeString.hashCode()
  }

  override fun toString(): String {
    return "$typeString.class"
  }
}

class LocalVariable(type: TypeMirror, val element: VarSymbol) : Reference(type) {
  constructor(node: LocalVariableNode) : this(node.type, node.element as VarSymbol)
  constructor(elem: Element) : this(ElementUtils.getType(elem), elem as VarSymbol)

  private val elementName = element.name.toString()
  private val ownerName = element.owner.toString()

  override fun isThisField(): Boolean {
    return false
  }

  override fun equals(other: Any?): Boolean {
    if (other !is LocalVariable) return false
    // The code below isn't just return vs.equals(vsother) because an element might be
    // different between subcheckers. The owner of a lambda parameter is the enclosing
    // method, so a local variable and a lambda parameter might have the same name and the
    // same owner. pos is used to differentiate this case.
    return element.pos == other.element.pos && other.elementName == elementName && other.ownerName == ownerName
  }

  override fun hashCode(): Int {
    var result = elementName.hashCode()
    result = 31 * result + ownerName.hashCode()
    return result
  }

  override fun toString(): String {
    return elementName
  }
}

class ReturnSpecialVar(type: TypeMirror) : Reference(type) {
  override fun isThisField(): Boolean {
    return false
  }

  override fun equals(other: Any?): Boolean {
    return other is ReturnSpecialVar
  }

  override fun hashCode(): Int {
    return 1
  }

  override fun toString(): String {
    return "#ret"
  }
}

// The "pos" distinguishes between different assignments
class OldSpecialVar(val reference: Reference, val pos: Int) : Reference(reference.type) {
  override fun isThisField(): Boolean {
    return false
  }

  override fun equals(other: Any?): Boolean {
    return other is OldSpecialVar && reference == other.reference && pos == other.pos
  }

  override fun hashCode(): Int {
    var result = reference.hashCode()
    result = 31 * result + pos
    return result
  }

  override fun toString(): String {
    return "old($reference)[$pos]"
  }
}
