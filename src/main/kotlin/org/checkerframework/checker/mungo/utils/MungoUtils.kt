package org.checkerframework.checker.mungo.utils

import com.sun.source.tree.IdentifierTree
import com.sun.source.tree.Tree
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.code.Symtab
import com.sun.tools.javac.code.Type
import com.sun.tools.javac.file.JavacFileManager
import com.sun.tools.javac.processing.JavacProcessingEnvironment
import com.sun.tools.javac.util.Log
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory
import org.checkerframework.checker.mungo.lib.MungoNullable
import org.checkerframework.checker.mungo.lib.MungoState
import org.checkerframework.checker.mungo.lib.MungoStateAfter
import org.checkerframework.checker.mungo.lib.MungoTypestate
import org.checkerframework.checker.mungo.qualifiers.MungoBottom
import org.checkerframework.checker.mungo.qualifiers.MungoInternalInfo
import org.checkerframework.checker.mungo.qualifiers.MungoUnknown
import org.checkerframework.checker.mungo.typecheck.MungoBottomType
import org.checkerframework.checker.mungo.typecheck.MungoType
import org.checkerframework.checker.mungo.typecheck.MungoUnknownType
import org.checkerframework.checker.mungo.typecheck.getTypeFromAnnotation
import org.checkerframework.checker.mungo.typestate.TypestateProcessor
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.javacutil.TypesUtils
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element
import javax.lang.model.type.TypeMirror
import javax.tools.JavaFileManager

class MungoUtils(val checker: MungoChecker) {

  class LazyField<T>(private val fn: () -> T) {
    private var value: T? = null
    fun get() = value ?: run {
      val v = fn()
      value = v
      v
    }
  }

  val ctx = (checker.processingEnvironment as JavacProcessingEnvironment).context
  val symtab = Symtab.instance(ctx)
  val log = Log.instance(ctx)
  val fileManager = ctx.get(JavaFileManager::class.java) as JavacFileManager

  val treeUtils = checker.treeUtils
  val typeUtils = checker.typeUtils

  val resolver = Resolver(checker)
  val classUtils = ClassUtils(this)
  val configUtils = ConfigUtils(checker.getConfigFile())

  val processor = TypestateProcessor(this)
  val methodUtils = MethodUtils(this)

  private var _factory: MungoAnnotatedTypeFactory? = null
  val factory get() = _factory ?: throw AssertionError("no factory")

  fun setFactory(f: MungoAnnotatedTypeFactory) {
    _factory = f
  }

  fun err(message: String, where: Tree) {
    checker.reportError(where, message)
  }

  fun err(message: String, where: Element) {
    checker.reportError(where, message)
  }

  fun err(message: String, file: Path, pos: Int) {
    checker.reportError(file, pos, message)
  }

  fun checkStates(graph: Graph, states: List<String>?): List<String> {
    if (states == null || states.isEmpty()) {
      return listOf("@MungoState should specify one or more states")
    }
    val basename = graph.resolvedFile.fileName
    return states.mapNotNull {
      if (graph.isFinalState(it)) {
        "State $it is final. Will have no effect in @MungoState"
      } else if (!graph.hasStateByName(it)) {
        "$basename has no $it state"
      } else null
    }
  }

  fun isSameType(a: Type?, b: Type?): Boolean {
    if (a == null) return b == null
    if (b == null) return false
    // isSameType for methods does not take thrown exceptions into account
    return typeUtils.isSameType(a, b) && isSameTypes(a.thrownTypes, b.thrownTypes)
  }

  fun isSameTypes(aList: List<Type?>, bList: List<Type?>): Boolean {
    if (aList.size != bList.size) {
      return false
    }
    val bIt = bList.iterator()
    for (a in aList) {
      val b = bIt.next()
      if (!isSameType(a, b)) {
        return false
      }
    }
    return true
  }

  fun getPath(tree: Tree): TreePath? = treeUtils.getPath(factory.getCurrentRoot(), tree)

  fun wasMovedToDiffClosure(path: TreePath, tree: IdentifierTree, element: Symbol.VarSymbol): Boolean {
    // See if it has protocol
    classUtils.visitClassOfElement(element) ?: return false

    // If "this"...
    if (TreeUtils.isExplicitThisDereference(tree)) {
      val enclosingMethodOrLambda = enclosingMethodOrLambda(path) ?: return false
      return enclosingMethodOrLambda.leaf.kind == Tree.Kind.LAMBDA_EXPRESSION
    }

    // Find declaration and enclosing method/lambda
    val declarationTree = factory.declarationFromElement(element) ?: return false
    val declaration = treeUtils.getPath(path.compilationUnit, declarationTree) ?: return false
    val enclosingMethodOrLambda = enclosingMethodOrLambda(path) ?: return false

    // See if variable declaration is enclosed in the enclosing method or lambda or not
    var path1: TreePath? = declaration
    var path2: TreePath? = enclosingMethodOrLambda
    while (path1 != null && path2 != null && path1 != enclosingMethodOrLambda) {
      path1 = path1.parentPath
      path2 = path2.parentPath
    }

    // Was moved if:
    // 1. Declaration is closer to the root (path1 == null && path2 != null)
    // 2. Both are at the same level (path1 == null && path2 == null) and identifier is enclosed in a lambda
    return path1 == null && (path2 != null || enclosingMethodOrLambda.leaf.kind == Tree.Kind.LAMBDA_EXPRESSION)
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
    val mungoStateAfterName: String = MungoStateAfter::class.java.canonicalName
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

    fun isMungoLibAnnotation(annotation: AnnotationMirror): Boolean {
      val name = AnnotationUtils.annotationName(annotation)
      return name == mungoStateName ||
        name == mungoStateAfterName ||
        typestateAnnotations.contains(name) ||
        nullableAnnotations.contains(name)
    }

    fun isMungoInternalAnnotation(annotation: AnnotationMirror): Boolean {
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

    fun getAnnotationValue(annotationMirror: AnnotationMirror?): List<String>? {
      if (annotationMirror == null) return null
      val value = AnnotationUtils.getElementValueArray(annotationMirror, "value", String::class.java, false)
      if (value.isEmpty()) return null
      return value
    }

    fun isBoolean(type: TypeMirror): Boolean {
      return TypesUtils.isBooleanType(type)
    }

    fun isEnum(type: TypeMirror): Boolean {
      return (type as Type).tsym.isEnum
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

    val cwd = Paths.get("").toAbsolutePath()

    fun getUserPath(p: Path): Path = if (p.isAbsolute) cwd.relativize(p) else p

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
