package jatyc.utils

import com.sun.source.tree.CompilationUnitTree
import com.sun.source.tree.IdentifierTree
import com.sun.source.tree.Tree
import com.sun.source.util.TreePath
import com.sun.source.util.Trees
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.code.Symtab
import com.sun.tools.javac.code.Type
import com.sun.tools.javac.code.TypeTag
import com.sun.tools.javac.file.JavacFileManager
import com.sun.tools.javac.processing.JavacProcessingEnvironment
import com.sun.tools.javac.tree.JCTree.JCClassDecl
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit
import com.sun.tools.javac.util.*
import com.sun.tools.javac.util.DefinedBy.Api
import jatyc.lib.*
import jatyc.typestate.TypestateProcessor
import jatyc.typestate.graph.Graph
import org.checkerframework.framework.source.SourceChecker
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.javacutil.BugInCF
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.javacutil.TypesUtils
import java.io.IOException
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element
import javax.lang.model.type.TypeKind
import javax.lang.model.type.TypeMirror
import javax.lang.model.util.Elements
import javax.lang.model.util.Types
import javax.tools.Diagnostic
import javax.tools.JavaFileManager
import javax.tools.JavaFileObject

class JTCUtils(val checker: SourceChecker) {
  val env = (checker.processingEnvironment as JavacProcessingEnvironment)
  val ctx: Context = env.context
  val symtab: Symtab = Symtab.instance(ctx)

  // val maker: TreeMaker = TreeMaker.instance(ctx)
  val fileManager = ctx.get(JavaFileManager::class.java) as JavacFileManager
  val treeUtils: Trees = checker.treeUtils
  val typeUtils: Types = checker.typeUtils
  val elementUtils: Elements = checker.elementUtils
  val resolver = Resolver(checker)
  val classUtils = ClassUtils(this)
  val configUtils = ConfigUtils(checker)
  val processor = TypestateProcessor(this)
  val methodUtils = MethodUtils(this)
  lateinit var factory: TypeFactory

  fun initFactory() {
    factory = TypeFactory(checker)
  }

  fun getTypeFromStub(elt: Element) = factory.getTypeFromStub(elt)

  // Adapted from SourceChecker#report and JavacTrees#printMessage
  private fun report(file: Path, pos: Int, messageKey: String, isError: Boolean, vararg args: Any?) {
    val defaultFormat = "($messageKey)"
    val fmtString = if (env.options != null && env.options.containsKey("nomsgtext")) {
      defaultFormat
    } else if (env.options != null && env.options.containsKey("detailedmsgtext")) {
      // TODO detailedMsgTextPrefix(source, defaultFormat, args) + fullMessageOf(messageKey, defaultFormat)
      defaultFormat
    } else {
      // TODO "[" + suppressionKey(messageKey) + "] " + fullMessageOf(messageKey, defaultFormat)
      defaultFormat
    }
    val messageText = try {
      String.format(fmtString, *args)
    } catch (e: Exception) {
      throw BugInCF("Invalid format string: \"$fmtString\" args: " + args.contentToString(), e)
    }
    val newSource = fileManager.getJavaFileObject(getUserPath(file))
    val tree = object : JCCompilationUnit(com.sun.tools.javac.util.List.nil()) {
      override fun pos(): JCDiagnostic.DiagnosticPosition {
        return JCDiagnostic.SimpleDiagnosticPosition(pos)
      }

      override fun getSourceFile(): JavaFileObject {
        return newSource
      }
    }

    if (isError) {
      treeUtils.printMessage(Diagnostic.Kind.ERROR, messageText, tree, tree)
    } else {
      treeUtils.printMessage(Diagnostic.Kind.MANDATORY_WARNING, messageText, tree, tree)
    }
  }

  fun err(message: String, where: Tree) {
    checker.reportError(where, message)
  }

  fun err(message: String, where: Element) {
    checker.reportError(where, message)
  }

  fun warn(message: String, where: Tree) {
    checker.reportWarning(where, message)
  }

  fun warn(message: String, where: Element) {
    checker.reportWarning(where, message)
  }

  fun err(message: String, file: Path, pos: Int) {
    report(file, pos, message, true)
  }

  fun warn(message: String, file: Path, pos: Int) {
    report(file, pos, message, false)
  }

  fun checkStates(graph: Graph, states: List<String>?): List<String> {
    if (states.isNullOrEmpty()) {
      return listOf("@Requires should specify one or more states")
    }
    val basename = graph.resolvedFile.fileName
    return states.mapNotNull {
      if (graph.isFinalState(it)) {
        "State $it is final. Will have no effect in @Requires"
      } else if (!graph.hasStateByName(it)) {
        "$basename has no $it state"
      } else null
    }
  }

  fun leastUpperBound(a: TypeMirror, b: TypeMirror): TypeMirror {
    // Avoid assertion error in com.sun.tools.javac.code.Types$SameTypeVisitor.visitType(Types.java:1064)
    if ((a as Type).tag == TypeTag.UNKNOWN) return a
    if ((b as Type).tag == TypeTag.UNKNOWN) return b
    return TypesUtils.leastUpperBound(a, b, env)
  }

  fun mostSpecific(a: TypeMirror, b: TypeMirror): TypeMirror {
    if (a.kind == TypeKind.EXECUTABLE || b.kind == TypeKind.EXECUTABLE) {
      // Avoid java.lang.IllegalArgumentException exception
      return a
    }
    return when {
      typeUtils.isAssignable(a, b) -> a
      typeUtils.isAssignable(b, a) -> b
      TypesUtils.isErasedSubtype(a, b, typeUtils) -> a
      TypesUtils.isErasedSubtype(b, a, typeUtils) -> b
      else -> a
    }
  }

  enum class CastType { INVALID, UPCAST, DOWNCAST }

  fun checkCastType(a: TypeMirror, b: TypeMirror): CastType {
    if (a.kind == TypeKind.EXECUTABLE || b.kind == TypeKind.EXECUTABLE) {
      // Avoid java.lang.IllegalArgumentException exception
      return CastType.INVALID
    }
    return when {
      typeUtils.isSubtype(a, b) -> CastType.DOWNCAST
      typeUtils.isSubtype(b, a) -> CastType.UPCAST
      TypesUtils.isErasedSubtype(a, b, typeUtils) -> CastType.DOWNCAST
      TypesUtils.isErasedSubtype(b, a, typeUtils) -> CastType.UPCAST
      else -> CastType.INVALID
    }
  }

  fun isSameType(a: TypeMirror?, b: TypeMirror?): Boolean {
    return a === b || isSameType(a as Type?, b as Type?)
  }

  fun isSameType(a: Type?, b: Type?): Boolean {
    if (a == null) return b == null
    if (b == null) return false
    if (a.tag == TypeTag.UNKNOWN) return b.tag == TypeTag.UNKNOWN
    if (b.tag == TypeTag.UNKNOWN) return a.tag == TypeTag.UNKNOWN
    // isSameType for methods does not take thrown exceptions into account
    // TODO ignore exceptions while we do not support them in typestates
    return typeUtils.isSameType(a, b) // && isSameTypes(a.thrownTypes, b.thrownTypes)
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

  fun getPath(tree: Tree, root: CompilationUnitTree): TreePath? = treeUtils.getPath(root, tree)

  fun wasMovedToDiffClosure(path: TreePath, tree: IdentifierTree, element: Symbol.VarSymbol): Boolean {
    // See if it has protocol
    classUtils.visitClassOfElement(element) ?: return false
    // If "this"...
    if (TreeUtils.isExplicitThisDereference(tree)) {
      val enclosingMethodOrLambda = enclosingMethodOrLambda(path) ?: return false
      return enclosingMethodOrLambda.leaf.kind == Tree.Kind.LAMBDA_EXPRESSION
    }
    // Find declaration and enclosing method/lambda
    val declarationTree = treeUtils.getTree(element) ?: return false
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
    // Add class pattern "jatyc.utils.JTCUtils"
    // and method name "breakpoint"
    // to IntelliJ's breakpoints settings
    println("--------")
  }

  companion object {
    val jtcRequiresAnno: String = Requires::class.java.canonicalName
    val jtcEnsuresAnno: String = Ensures::class.java.canonicalName
    val typestateAnnotations = setOf(Typestate::class.java.canonicalName, "mungo.lib.Typestate")
    val nullableAnnotations = setOf(
      Nullable::class.java.canonicalName,
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

    fun isLibAnnotation(annotation: AnnotationMirror): Boolean {
      val name = AnnotationUtils.annotationName(annotation)
      return name == jtcRequiresAnno ||
        name == jtcEnsuresAnno ||
        typestateAnnotations.contains(name) ||
        nullableAnnotations.contains(name)
    }

    fun getAnnotationValue(annotationMirror: AnnotationMirror?): List<String>? {
      if (annotationMirror == null) return null
      val value = AnnotationUtils.getElementValueArray(annotationMirror, "value", String::class.java, false)
      if (value.isEmpty()) return null
      return value
    }

    fun hasAnnotation(type: AnnotatedTypeMirror, annotation: String): Boolean {
      return type.annotations.any {
        AnnotationUtils.annotationName(it) == annotation
      }
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

    val cwd: Path = Paths.get("").toAbsolutePath()

    fun getUserPath(p: Path): Path = if (p.isAbsolute) cwd.relativize(p) else p

    fun printStack() {
      try {
        throw RuntimeException("debug")
      } catch (exp: RuntimeException) {
        exp.printStackTrace()
      }
    }

  }

}
