package org.checkerframework.checker.mungo.utils

import com.sun.source.tree.Tree
import com.sun.source.util.TreePath
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory
import org.checkerframework.checker.mungo.lib.MungoNullable
import org.checkerframework.checker.mungo.lib.MungoState
import org.checkerframework.checker.mungo.lib.MungoTypestate
import org.checkerframework.checker.mungo.qualifiers.MungoBottom
import org.checkerframework.checker.mungo.qualifiers.MungoInternalInfo
import org.checkerframework.checker.mungo.qualifiers.MungoUnknown
import org.checkerframework.checker.mungo.typecheck.MungoBottomType
import org.checkerframework.checker.mungo.typecheck.MungoType
import org.checkerframework.checker.mungo.typecheck.MungoUnknownType
import org.checkerframework.checker.mungo.typecheck.getTypeFromAnnotation
import org.checkerframework.checker.mungo.typestate.TypestateProcessor
import org.checkerframework.framework.source.Result
import org.checkerframework.javacutil.AnnotationUtils
import java.nio.file.Path
import java.util.*
import javax.lang.model.element.AnnotationMirror

class MungoUtils(val checker: MungoChecker) {

  val resolver = Resolver(checker.processingEnvironment)
  val classUtils = ClassUtils(this)

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
    val mungoStateName: String = MungoState::class.java.canonicalName
    val typestateAnnotations = setOf(MungoTypestate::class.java.canonicalName, "mungo.lib.Typestate")
    val nullableAnnotations = setOf(
      MungoNullable::class.java.canonicalName,
      // From https://github.com/JetBrains/kotlin/blob/master/core/descriptors.jvm/src/org/jetbrains/kotlin/load/java/JvmAnnotationNames.kt
      "org.jetbrains.annotations.Nullable",
      "androidx.annotation.Nullable",
      "android.support.annotation.Nullable",
      "android.annotation.Nullable",
      "com.android.annotations.Nullable",
      "org.eclipse.jdt.annotation.Nullable",
      "org.checkerframework.checker.nullness.qual.Nullable",
      "javax.annotation.Nullable",
      "javax.annotation.CheckForNull",
      "edu.umd.cs.findbugs.annotations.CheckForNull",
      "edu.umd.cs.findbugs.annotations.Nullable",
      "edu.umd.cs.findbugs.annotations.PossiblyNull",
      "io.reactivex.annotations.Nullable"
    )

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

    // Adapted from TreeUtils.enclosingMethodOrLambda to return a TreePath instead of Tree
    fun enclosingMethodOrLambda(path: TreePath): TreePath? {
      return enclosingOfKind(path, EnumSet.of(Tree.Kind.METHOD, Tree.Kind.LAMBDA_EXPRESSION))
    }

    // Adapted from TreeUtils.enclosingOfKind to return a TreePath instead of Tree
    private fun enclosingOfKind(path: TreePath, kinds: Set<Tree.Kind>): TreePath? {
      var p: TreePath? = path
      while (p != null) {
        val leaf = p.leaf
        if (kinds.contains(leaf.kind)) {
          return p
        }
        p = p.parentPath
      }
      return null
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
