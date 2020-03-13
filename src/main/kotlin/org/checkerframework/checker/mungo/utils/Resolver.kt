package org.checkerframework.checker.mungo.utils

import org.checkerframework.javacutil.Resolver
import com.sun.source.util.TreePath
import javax.annotation.processing.ProcessingEnvironment
import javax.lang.model.element.Element

class Resolver(env: ProcessingEnvironment) {

  private val resolver = Resolver(env)

  fun resolve(path: TreePath, name: String): Element {
    return resolver.findClass(name, path)
  }

}
