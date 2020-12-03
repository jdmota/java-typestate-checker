package org.checkerframework.checker.mungo.utils

import com.sun.source.tree.*
import org.checkerframework.javacutil.TreeUtils
import javax.lang.model.element.Element
import javax.lang.model.type.TypeMirror
import javax.lang.model.type.TypeVariable
import javax.lang.model.type.WildcardType

fun treeToType(tree: Tree): TypeMirror = when (tree) {
  is ClassTree -> TreeUtils.elementFromDeclaration(tree).asType()
  is MethodTree -> TreeUtils.elementFromDeclaration(tree).asType()
  is VariableTree -> TreeUtils.elementFromDeclaration(tree).asType()
  is ExpressionTree -> TreeUtils.typeOf(TreeUtils.withoutParens(tree))
  else -> throw RuntimeException("unknown kind ${tree.kind}")
}

fun treeToElement(tree: Tree): Element = when (tree) {
  is ClassTree -> TreeUtils.elementFromDeclaration(tree)
  is MethodTree -> TreeUtils.elementFromDeclaration(tree)
  is VariableTree -> TreeUtils.elementFromDeclaration(tree)
  else -> throw RuntimeException("unknown kind ${tree.kind}")
}

// Adapted from TreeUtils.isSelfAccess
fun isSelfAccess(tree: ExpressionTree): Boolean {
  var tr = TreeUtils.withoutParens(tree)
  if (tr.kind == Tree.Kind.ARRAY_ACCESS) {
    return false
  }

  if (tree is MethodInvocationTree) {
    tr = tree.methodSelect
  }
  tr = TreeUtils.withoutParens(tr)

  if (tr is TypeCastTree) {
    tr = tr.expression
  }
  tr = TreeUtils.withoutParens(tr)

  if (tr.kind == Tree.Kind.IDENTIFIER) {
    return true
  }

  if (tr is MemberSelectTree) {
    tr = tr.expression
    // Fix missing
    return TreeUtils.isExplicitThisDereference(tr)
  }

  return false
}

fun upperBound(type: TypeMirror): TypeMirror {
  var type = type
  loop@ do {
    type = when (type) {
      is TypeVariable -> if (type.upperBound != null) type.upperBound else break@loop
      is WildcardType -> if (type.extendsBound != null) type.extendsBound else break@loop
      else -> break@loop
    }
  } while (true)
  return type
}

fun lowerBound(type: TypeMirror): TypeMirror {
  var type = type
  loop@ do {
    type = when (type) {
      is TypeVariable -> if (type.lowerBound != null) type.lowerBound else break@loop
      is WildcardType -> if (type.superBound != null) type.superBound else break@loop
      else -> break@loop
    }
  } while (true)
  return type
}
