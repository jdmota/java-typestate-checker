package org.checkerframework.checker.mungo.utils

import com.sun.source.tree.*
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Type
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory
import org.checkerframework.checker.mungo.lib.MungoTypestate
import org.checkerframework.checker.mungo.qualifiers.MungoBottom
import org.checkerframework.checker.mungo.qualifiers.MungoInfo
import org.checkerframework.checker.mungo.qualifiers.MungoUnknown
import org.checkerframework.checker.mungo.typecheck.MungoBottomType
import org.checkerframework.checker.mungo.typecheck.MungoConcreteType
import org.checkerframework.checker.mungo.typecheck.MungoType
import org.checkerframework.checker.mungo.typecheck.MungoUnknownType
import org.checkerframework.checker.mungo.typestate.TypestateProcessor
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.framework.source.Result
import org.checkerframework.javacutil.AnnotationBuilder
import org.checkerframework.javacutil.AnnotationUtils
import java.nio.file.Path
import java.nio.file.Paths
import javax.annotation.processing.ProcessingEnvironment
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

  private fun getGraphFromAnnotation(annoMirror: AnnotationMirror): Graph? {
    for ((_, value) in annoMirror.elementValues) {
      val file = value.value as String
      return processor.lookupGraph(Paths.get(file))
    }
    return null
  }

  fun mungoTypeFromAnnotations(annotations: Collection<AnnotationMirror>): MungoType {
    for (annoMirror in annotations) {
      if (AnnotationUtils.areSameByName(annoMirror, mungoInfoName)) {
        val graph = getGraphFromAnnotation(annoMirror)
        return if (graph == null) MungoUnknownType() else MungoConcreteType(graph, graph.getAllConcreteStates())
      }
      if (AnnotationUtils.areSameByName(annoMirror, mungoUnknownName)) {
        return MungoUnknownType()
      }
      if (AnnotationUtils.areSameByName(annoMirror, mungoBottomName)) {
        return MungoBottomType()
      }
    }
    return MungoUnknownType()
  }

  fun breakpoint() {
    // For debugging purposes
    // Add class pattern "org.checkerframework.checker.mungo.utils.MungoUtils"
    // and method name "breakpoint"
    // to IntelliJ's breakpoints settings
    println("--------")
  }

  companion object {
    val mungoTypestateName: String = MungoTypestate::class.java.canonicalName
    val mungoInfoName: String = MungoInfo::class.java.canonicalName
    val mungoBottomName: String = MungoBottom::class.java.canonicalName
    val mungoUnknownName: String = MungoUnknown::class.java.canonicalName

    fun buildAnnotation(env: ProcessingEnvironment, file: Path): AnnotationMirror {
      val builder = AnnotationBuilder(env, MungoInfo::class.java)
      builder.setValue("file", file.toString())
      return builder.build()
    }

    fun printStack() {
      try {
        throw RuntimeException("debug")
      } catch (exp: RuntimeException) {
        exp.printStackTrace()
      }
    }

    fun <T> printResult(prefix: String, ret: T): T {
      println("$prefix $ret")
      return ret
    }
  }

}
