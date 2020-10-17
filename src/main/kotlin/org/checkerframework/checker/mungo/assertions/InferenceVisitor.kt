package org.checkerframework.checker.mungo.assertions

import com.sun.source.tree.ClassTree
import com.sun.source.tree.CompilationUnitTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.framework.source.SourceVisitor

class InferenceVisitor(val checker: MungoChecker) : SourceVisitor<Void?, Void?>(checker) {

  val inferrer = Inferrer(checker)
  private val utils get() = checker.utils

  override fun visitCompilationUnit(node: CompilationUnitTree, p: Void?): Void? {
    return scan(node.typeDecls, p)
  }

  override fun visitClass(classTree: ClassTree, p: Void?): Void? {
    utils.factory.setRoot(root)
    inferrer.setRoot(root)
    inferrer.run(classTree)
    return null
  }

}
