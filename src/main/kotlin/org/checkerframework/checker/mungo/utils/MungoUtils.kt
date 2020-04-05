package org.checkerframework.checker.mungo.utils

import com.sun.source.tree.*
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Type
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory
import org.checkerframework.checker.mungo.lib.MungoNullable
import org.checkerframework.checker.mungo.lib.MungoTypestate
import org.checkerframework.checker.mungo.lib.MungoState
import org.checkerframework.checker.mungo.qualifiers.MungoBottom
import org.checkerframework.checker.mungo.qualifiers.MungoInternalInfo
import org.checkerframework.checker.mungo.qualifiers.MungoUnknown
import org.checkerframework.checker.mungo.typecheck.*
import org.checkerframework.checker.mungo.typestate.TypestateProcessor
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.framework.source.Result
import org.checkerframework.javacutil.AnnotationUtils
import java.nio.file.Path
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element

class MungoUtils(val checker: MungoChecker) {

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

  fun err(message: String, where: Any) {
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

  fun visitClassTree(treePath: TreePath, tree: ClassTree): Graph? {
    return classProcessor.visitClassTree(treePath, tree)
  }

  fun checkStates(file: Path, states: List<String>, src: Any) {
    val graph = processor.lookupGraph(file)
    val basename = file.fileName
    for (state in states) {
      if (graph.isFinalState(state)) {
        err("State $state is final. Will have no effect in @MungoState", src)
      } else if (!graph.hasStateByName(state)) {
        err("$basename has no $state state", src)
      }
    }
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
    val mungoStateName: String = MungoState::class.java.canonicalName
    val mungoNullableName: String = MungoNullable::class.java.canonicalName

    // Internal annotations for type information
    val mungoUnknownName: String = MungoUnknown::class.java.canonicalName
    val mungoInternalInfoName: String = MungoInternalInfo::class.java.canonicalName
    val mungoBottomName: String = MungoBottom::class.java.canonicalName

    fun isMungoAnnotation(annotation: AnnotationMirror): Boolean {
      return AnnotationUtils.areSameByName(annotation, mungoUnknownName) ||
        AnnotationUtils.areSameByName(annotation, mungoInternalInfoName) ||
        AnnotationUtils.areSameByName(annotation, mungoBottomName)
    }

    fun mungoTypeFromAnnotation(annotation: AnnotationMirror): MungoType {
      if (AnnotationUtils.areSameByName(annotation, mungoUnknownName)) {
        return MungoUnknownType.SINGLETON
      }
      if (AnnotationUtils.areSameByName(annotation, mungoInternalInfoName)) {
        return getTypeFromAnnotation(annotation)
      }
      if (AnnotationUtils.areSameByName(annotation, mungoBottomName)) {
        return MungoBottomType.SINGLETON
      }
      throw AssertionError("mungoTypeFromAnnotation")
    }

    fun mungoTypeFromAnnotations(annotations: Collection<AnnotationMirror>): MungoType {
      for (annotation in annotations) {
        if (AnnotationUtils.areSameByName(annotation, mungoUnknownName)) {
          return MungoUnknownType.SINGLETON
        }
        if (AnnotationUtils.areSameByName(annotation, mungoInternalInfoName)) {
          return getTypeFromAnnotation(annotation)
        }
        if (AnnotationUtils.areSameByName(annotation, mungoBottomName)) {
          return MungoBottomType.SINGLETON
        }
      }
      return MungoUnknownType.SINGLETON
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
