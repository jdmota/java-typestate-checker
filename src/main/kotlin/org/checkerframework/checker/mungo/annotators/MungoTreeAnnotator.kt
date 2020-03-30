package org.checkerframework.checker.mungo.annotators

import com.sun.source.tree.LiteralTree
import com.sun.source.tree.NewClassTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.qualifiers.MungoInternalInfo
import org.checkerframework.checker.mungo.typecheck.MungoNoProtocolType
import org.checkerframework.checker.mungo.typecheck.MungoNullType
import org.checkerframework.checker.mungo.typecheck.createTypeWithAllStates
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.framework.type.treeannotator.TreeAnnotator
import java.nio.file.Paths

class MungoTreeAnnotator(private val checker: MungoChecker, atypeFactory: MungoAnnotatedTypeFactory) : TreeAnnotator(atypeFactory) {
  override fun visitNewClass(node: NewClassTree, annotatedTypeMirror: AnnotatedTypeMirror): Void? {
    val tree = node.classBody
    if (tree != null && !annotatedTypeMirror.hasAnnotation(MungoInternalInfo::class.java)) {
      // Here we handle anonymous classes because doing this in MungoDefaultQualifierForUseTypeAnnotator is not enough
      val graph = checker.utils.visitClassTree(Paths.get(atypeFactory.visitorState.path.compilationUnit.sourceFile.toUri()), tree)
      if (graph != null) {
        val annotation = createTypeWithAllStates(graph).buildAnnotation(checker.processingEnvironment)
        annotatedTypeMirror.replaceAnnotation(annotation)
      }
    }
    return null
  }

  override fun visitLiteral(node: LiteralTree, annotatedTypeMirror: AnnotatedTypeMirror): Void? {
    val ret = super.visitLiteral(node, annotatedTypeMirror)
    if (node.value == null) {
      annotatedTypeMirror.replaceAnnotation(MungoNullType.SINGLETON.buildAnnotation(checker.processingEnvironment))
    } else {
      annotatedTypeMirror.replaceAnnotation(MungoNoProtocolType.SINGLETON.buildAnnotation(checker.processingEnvironment))
    }
    return ret
  }
}
