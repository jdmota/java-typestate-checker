package org.checkerframework.checker.mungo.utils

import com.sun.source.tree.*
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory
import org.checkerframework.checker.mungo.qualifiers.MungoInfo
import org.checkerframework.checker.mungo.typecheck.MungoTypeInfo
import org.checkerframework.checker.mungo.typestate.TypestateProcessor
import org.checkerframework.checker.mungo.typestate.ast.TMethodNode
import org.checkerframework.framework.source.Result
import org.checkerframework.javacutil.AnnotationUtils
import java.nio.file.Path
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element

class MungoUtils(val checker: MungoChecker) {

  val factory = checker.typeFactory as MungoAnnotatedTypeFactory
  val processor = TypestateProcessor()
  private val resolver = Resolver(checker.processingEnvironment)
  private val classProcessor = ClassUtils(this)
  private val methodUtils = MethodUtils(checker.processingEnvironment)

  fun err(message: String, where: Tree) {
    checker.report(Result.failure(message), where)
  }

  fun resolve(path: TreePath, name: String): Element {
    return resolver.resolve(path, name)
  }

  fun visitClassSymbol(element: Element?): MungoTypeInfo? {
    return classProcessor.visitClassSymbol(element)
  }

  fun visitClassTree(sourceFilePath: Path, tree: ClassTree): MungoTypeInfo? {
    return classProcessor.visitClassTree(sourceFilePath, tree)
  }

  fun methodNodeToMethodSymbol(node: TMethodNode, owner: Symbol): Symbol.MethodSymbol {
    return methodUtils.methodNodeToMethodSymbol(node, owner)
  }

  companion object {
    private val mungoInfoName = MungoInfo::class.java.canonicalName // Cache name

    fun getInfoFromAnnotations(annotations: Collection<AnnotationMirror>): MungoTypeInfo? {
      for (annoMirror in annotations) {
        if (AnnotationUtils.areSameByName(annoMirror, mungoInfoName)) {
          return annoMirror as MungoTypeInfo
        }
      }
      return null
    }

    fun castAnnotation(annoMirror: AnnotationMirror): MungoTypeInfo {
      return annoMirror as MungoTypeInfo
    }
  }

}
