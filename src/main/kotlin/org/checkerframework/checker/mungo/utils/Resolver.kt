package org.checkerframework.checker.mungo.utils

import org.checkerframework.javacutil.Resolver
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.code.Symtab
import com.sun.tools.javac.code.Type
import com.sun.tools.javac.processing.JavacProcessingEnvironment
import javax.annotation.processing.ProcessingEnvironment
import javax.lang.model.element.Element

class Resolver(env: ProcessingEnvironment) {

  private val resolver = Resolver(env)
  private val symtab = Symtab.instance((env as JavacProcessingEnvironment).context)

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

  fun resolve(path: TreePath, name: String): Type? {
    return when (name) {
      "byte" -> symtab.byteType
      "char" -> symtab.charType
      "short" -> symtab.shortType
      "int" -> symtab.intType
      "long" -> symtab.longType
      "float" -> symtab.floatType
      "double" -> symtab.doubleType
      "boolean" -> symtab.booleanType
      "void" -> symtab.voidType
      else -> {
        val t = (resolver.findClass(name, path) as Symbol?)?.type
        // println("Resolving $name to $t")
        t
      }
    }
  }

}
