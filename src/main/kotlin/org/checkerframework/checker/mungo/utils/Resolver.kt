package org.checkerframework.checker.mungo.utils

import org.checkerframework.javacutil.Resolver
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.code.Symtab
import com.sun.tools.javac.code.Type
import com.sun.tools.javac.processing.JavacProcessingEnvironment
import javax.annotation.processing.ProcessingEnvironment

class Resolver(env: ProcessingEnvironment) {

  private val resolver = Resolver(env)
  private val symtab = Symtab.instance((env as JavacProcessingEnvironment).context)

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
        val parts = name.split(".")
        if (parts.size == 1) {
          (resolver.findClass(parts[0], path) as? Symbol)?.type
        } else {
          // So that things like java.lang.Object can be resolved
          val pkgName = parts.subList(0, parts.size - 1).joinToString(".")
          val pkg = resolver.findPackage(pkgName, path) ?: return null
          val className = parts[parts.lastIndex]
          resolver.findClassInPackage(className, pkg, path)?.asType()
        }
      }
    }
  }

}
