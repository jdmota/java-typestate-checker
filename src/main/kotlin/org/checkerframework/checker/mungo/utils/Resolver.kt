package org.checkerframework.checker.mungo.utils

import org.checkerframework.javacutil.Resolver
import com.sun.source.util.TreePath
import javax.annotation.processing.ProcessingEnvironment
import javax.lang.model.element.Element

class Resolver(env: ProcessingEnvironment) {

  private val resolver = Resolver(env)

  // FIXME works with "Object" but not with "java.lang.Object" ??

  /*
  val unit = n.treePath.compilationUnit as JCTree.JCCompilationUnit
  val sym = c.getUtils().resolve(n.treePath, "java.lang.Object")
  println(sym)
  println(sym::class.java)

  val sym2 = c.getUtils().resolve(n.treePath, "Object")
  println(sym2)
  println(sym2::class.java) // Expected to be ClassSymbol
   */

  fun resolve(path: TreePath, name: String): Element {
    return resolver.findClass(name, path)
  }

}
