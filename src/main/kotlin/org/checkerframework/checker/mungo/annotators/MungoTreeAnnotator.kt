package org.checkerframework.checker.mungo.annotators

import com.sun.source.tree.LiteralTree
import com.sun.source.tree.NewClassTree
import com.sun.source.tree.Tree
import com.sun.source.tree.VariableTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.qualifiers.MungoInternalInfo
import org.checkerframework.checker.mungo.typecheck.MungoNoProtocolType
import org.checkerframework.checker.mungo.typecheck.MungoNullType
import org.checkerframework.checker.mungo.typecheck.MungoPrimitiveType
import org.checkerframework.checker.mungo.typecheck.createTypeWithAllStates
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.framework.type.treeannotator.TreeAnnotator

class MungoTreeAnnotator(private val checker: MungoChecker, private val factory: MungoAnnotatedTypeFactory) : TreeAnnotator(factory) {
  override fun visitNewClass(node: NewClassTree, annotatedTypeMirror: AnnotatedTypeMirror): Void? {
    val tree = node.classBody
    if (tree != null && !annotatedTypeMirror.hasAnnotation(MungoInternalInfo::class.java)) {
      // Here we handle anonymous classes because doing this in MungoDefaultQualifierForUseTypeAnnotator is not enough
      val graph = checker.utils.classUtils.visitClassTree(factory.getPath(tree))
      if (graph != null) {
        val annotation = createTypeWithAllStates(graph).buildAnnotation(checker.processingEnvironment)
        annotatedTypeMirror.replaceAnnotation(annotation)
      }
    }
    return null
  }

  override fun visitLiteral(node: LiteralTree, annotatedTypeMirror: AnnotatedTypeMirror): Void? {
    val ret = super.visitLiteral(node, annotatedTypeMirror)
    val type = when (node.kind) {
      Tree.Kind.NULL_LITERAL -> MungoNullType.SINGLETON
      Tree.Kind.STRING_LITERAL -> MungoNoProtocolType.SINGLETON
      else -> MungoPrimitiveType.SINGLETON
    }
    annotatedTypeMirror.replaceAnnotation(type.buildAnnotation(checker.processingEnvironment))
    return ret
  }

  override fun visitVariable(node: VariableTree, type: AnnotatedTypeMirror): Void? {
    val ret = super.visitVariable(node, type)
    if (type is AnnotatedTypeMirror.AnnotatedDeclaredType) {
      factory.visitDeclaredType(type, node)
    }
    return ret
  }
}
