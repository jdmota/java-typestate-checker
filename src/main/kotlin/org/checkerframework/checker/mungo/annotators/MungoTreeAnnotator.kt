package org.checkerframework.checker.mungo.annotators

import com.sun.source.tree.LiteralTree
import com.sun.source.tree.NewClassTree
import com.sun.source.tree.Tree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.qualifiers.MungoInfo
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.framework.type.treeannotator.TreeAnnotator
import java.nio.file.Paths

class MungoTreeAnnotator(private val checker: MungoChecker, atypeFactory: MungoAnnotatedTypeFactory) : TreeAnnotator(atypeFactory) {

  // FIXME null should not be the bottom type
  override fun defaultAction(node: Tree, type: AnnotatedTypeMirror): Void? {
    super.defaultAction(node, type)
    // type.addMissingAnnotations(fnd);
    return MungoUtils.printResult("defaultAction $node ${node.kind} ${node::class.java} ${type.annotations}", null)
  }

  override fun visitNewClass(node: NewClassTree, annotatedTypeMirror: AnnotatedTypeMirror): Void? {
    val tree = node.classBody
    if (tree != null && !annotatedTypeMirror.hasAnnotation(MungoInfo::class.java)) {
      // Here we handle anonymous classes because doing this in MungoDefaultQualifierForUseTypeAnnotator is not enough
      val graph = checker.utils.visitClassTree(Paths.get(atypeFactory.visitorState.path.compilationUnit.sourceFile.toUri()), tree)
      if (graph != null) {
        val anno = MungoUtils.buildAnnotation(checker.processingEnvironment, graph.file)
        annotatedTypeMirror.replaceAnnotation(anno)
      }
    }
    return null
  }
}
