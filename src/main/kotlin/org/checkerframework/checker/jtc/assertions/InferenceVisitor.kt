package org.checkerframework.checker.jtc.assertions

import com.sun.source.tree.ClassTree
import com.sun.source.tree.CompilationUnitTree
import org.checkerframework.checker.jtc.JavaTypestateChecker
import org.checkerframework.framework.source.SourceVisitor

class InferenceVisitor(val checker: JavaTypestateChecker) : SourceVisitor<Void?, Void?>(checker) {

  val inferrer = Inferrer(checker)
  private val utils get() = checker.utils

  override fun visitCompilationUnit(node: CompilationUnitTree, p: Void?): Void? {
    return scan(node.typeDecls, p)
  }

  override fun visitClass(classTree: ClassTree, p: Void?): Void? {
    utils.factory.setRoot(root)
    inferrer.setRoot(root)
    inferrer.phase1(classTree)
    return null
  }

}
