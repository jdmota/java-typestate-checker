package org.checkerframework.checker.mungo.utils

import com.sun.source.tree.*
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.code.Type
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory
import org.checkerframework.checker.mungo.lib.MungoTypestate
import org.checkerframework.checker.mungo.qualifiers.MungoBottom
import org.checkerframework.checker.mungo.qualifiers.MungoInfo
import org.checkerframework.checker.mungo.qualifiers.MungoUnknown
import org.checkerframework.checker.mungo.typecheck.MungoTypeInfo
import org.checkerframework.checker.mungo.typestate.TypestateProcessor
import org.checkerframework.checker.mungo.typestate.ast.TMethodNode
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.framework.source.Result
import org.checkerframework.javacutil.AnnotationBuilder
import org.checkerframework.javacutil.AnnotationUtils
import java.nio.file.Path
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element

class MungoUtils(val checker: MungoChecker) {

  val bottomAnnotation: AnnotationMirror = AnnotationBuilder.fromClass(checker.elementUtils, MungoBottom::class.java)
  val infoAnnotation: AnnotationMirror = AnnotationBuilder.fromClass(checker.elementUtils, MungoInfo::class.java)
  val unknownAnnotation: AnnotationMirror = AnnotationBuilder.fromClass(checker.elementUtils, MungoUnknown::class.java)

  private val resolver = Resolver(checker.processingEnvironment)
  private val classProcessor = ClassUtils(this)

  val processor = TypestateProcessor()
  val methodUtils = MethodUtils(this)

  private lateinit var _factory: MungoAnnotatedTypeFactory
  val factory: MungoAnnotatedTypeFactory
    get() {
      if (!this::_factory.isInitialized) {
        _factory = checker.typeFactory as MungoAnnotatedTypeFactory
      }
      return _factory
    }

  fun err(message: String, where: Tree) {
    checker.report(Result.failure(message), where)
  }

  fun resolve(path: TreePath, name: String): Type? {
    return resolver.resolve(path, name)
  }

  fun visitClassSymbol(element: Element?): Graph? {
    return classProcessor.visitClassSymbol(element)
  }

  fun visitClassTree(sourceFilePath: Path, tree: ClassTree): Graph? {
    return classProcessor.visitClassTree(sourceFilePath, tree)
  }

  companion object {
    val mungoInfoName = MungoInfo::class.java.canonicalName
    val mungoTypestateName = MungoTypestate::class.java.canonicalName
    val mungoBottomName = MungoBottom::class.java.canonicalName

    fun getInfoFromAnnotations(annotations: Collection<AnnotationMirror>): MungoTypeInfo? {
      for (annoMirror in annotations) {
        if (AnnotationUtils.areSameByName(annoMirror, mungoInfoName)) {
          return annoMirror as MungoTypeInfo
        }
      }
      return null
    }

    fun castAnnotation(annotation: AnnotationMirror): MungoTypeInfo {
      return annotation as MungoTypeInfo
    }

    fun hasBottom(annotations: Collection<AnnotationMirror>): Boolean {
      for (annoMirror in annotations) {
        if (AnnotationUtils.areSameByName(annoMirror, mungoBottomName)) {
          return true
        }
      }
      return false
    }
  }

}
