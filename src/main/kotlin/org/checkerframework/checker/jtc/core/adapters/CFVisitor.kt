package org.checkerframework.checker.jtc.core.adapters

import com.sun.source.tree.*
import com.sun.tools.javac.code.Flags
import com.sun.tools.javac.code.Symbol.MethodSymbol
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.jtc.JavaTypestateChecker
import org.checkerframework.checker.jtc.core.JavaTypesHierarchy
import org.checkerframework.checker.jtc.core.TypeIntroducer
import org.checkerframework.checker.jtc.core.linearmode.LinearModeClassAnalysis
import org.checkerframework.checker.jtc.core.TypecheckUtils
import org.checkerframework.checker.jtc.core.cfg.ClassDeclAndCompanion
import org.checkerframework.checker.jtc.utils.JTCUtils
import org.checkerframework.dataflow.qual.Pure
import org.checkerframework.dataflow.util.PurityChecker
import org.checkerframework.dataflow.util.PurityChecker.PurityResult
import org.checkerframework.dataflow.util.PurityUtils
import org.checkerframework.framework.source.SourceVisitor
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.javacutil.Pair
import java.util.*
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.ExecutableElement
import javax.lang.model.element.Modifier
import javax.lang.model.type.TypeKind

class CFVisitor(val checker: JavaTypestateChecker) : SourceVisitor<Void?, Void?>(checker) {

  private val utils get() = checker.utils
  private val javaTypesHierarchy = JavaTypesHierarchy(checker)
  private var typeIntroducer = TypeIntroducer(checker, javaTypesHierarchy)
  private val typecheckUtils = TypecheckUtils(checker, typeIntroducer)
  private val adapter = CFAdapter(checker, javaTypesHierarchy, typeIntroducer)
  private val classes = mutableMapOf<String, ClassDeclAndCompanion>()
  private val classAnalysis = LinearModeClassAnalysis(checker, javaTypesHierarchy, typeIntroducer, typecheckUtils, classes)
  private val pending = LinkedList<Pair<CompilationUnitTree, ClassDeclAndCompanion>>()

  override fun setRoot(root: CompilationUnitTree) {
    super.setRoot(root)
    adapter.setRoot(root)
  }

  override fun visitClass(classTree: ClassTree, p: Void?): Void? {
    val clazz = adapter.transformClass(classTree as JCTree.JCClassDecl)

    classes[classTree.sym.qualifiedName.toString()] = clazz

    pending.push(Pair.of(root, clazz))

    return super.visitClass(classTree, p)
  }

  // Called after all code was visited
  fun finishAnalysis() {
    while (pending.isNotEmpty()) {
      val next = pending.pop()
      checker.setCompilationRoot(next.first)
      analyze(next.second)
    }
  }

  private fun analyze(clazz: ClassDeclAndCompanion) {
    classAnalysis.analyze(clazz.nonStatic)
    classAnalysis.analyze(clazz.static)
    classAnalysis.checkMethods(clazz.nonStatic)

    val inference1 = classAnalysis.inference
    val inference2 = classAnalysis.inference.inference

    for ((codeExpr, warnings) in inference1.warnings) {
      val tree = inference2.getTree(codeExpr)
      val root = inference2.getRoot(codeExpr)
      checker.setCompilationRoot(root)
      for (warn in warnings) {
        checker.reportWarning(tree, warn)
      }
    }

    for ((codeExpr, error) in inference1.errors) {
      val tree = inference2.getTree(codeExpr)
      val root = inference2.getRoot(codeExpr)
      checker.setCompilationRoot(root)
      checker.reportError(tree, error)
    }

    for ((codeExpr, errors) in inference1.completionErrors) {
      val tree = inference2.getTree(codeExpr)
      val root = inference2.getRoot(codeExpr)
      checker.setCompilationRoot(root)
      for (error in errors) {
        checker.reportError(tree, error)
      }
    }

    for ((codeExpr, errors) in inference1.validationErrors) {
      val tree = inference2.getTree(codeExpr)
      val root = inference2.getRoot(codeExpr)
      checker.setCompilationRoot(root)
      for (error in errors) {
        checker.reportError(tree, error)
      }
    }

    inference1.warnings.clear()
    inference1.errors.clear()
    inference1.completionErrors.clear()
    inference1.validationErrors.clear()
  }

  override fun visitAnnotation(node: AnnotationTree, p: Void?): Void? {
    val annoMirror = TreeUtils.annotationFromAnnotationTree(node)
    val parent = currentPath.parentPath.parentPath.leaf
    val parentParent = currentPath.parentPath.parentPath.parentPath.leaf
    val annotationName = AnnotationUtils.annotationName(annoMirror)

    when (annotationName) {
      JTCUtils.jtcStateAnno -> checkReturnTypeAnnotation(node, annoMirror, parent)
      JTCUtils.jtcRequiresAnno -> checkParameterAnnotation(node, annoMirror, parent, parentParent, "Requires")
      JTCUtils.jtcEnsuresAnno -> checkParameterAnnotation(node, annoMirror, parent, parentParent, "Ensures")
    }

    if (JTCUtils.typestateAnnotations.contains(annotationName)) {
      if (parent !is ClassTree || !parent.modifiers.annotations.contains(node)) {
        utils.err("@Typestate should go on classes or interfaces", node)
      }
    }

    return null
  }

  private fun checkReturnTypeAnnotation(node: AnnotationTree, annoMirror: AnnotationMirror, parent: Tree) {
    if (parent is MethodTree && parent.modifiers.annotations.contains(node)) {
      val typeMirror = TreeUtils.elementFromTree(parent.returnType)!!.asType()
      val graph = utils.classUtils.visitClassTypeMirror(typeMirror)
      if (graph == null) {
        utils.err("@State has no meaning since this type has no protocol", node)
      } else {
        val stateNames = JTCUtils.getAnnotationValue(annoMirror)
        utils.checkStates(graph, stateNames).forEach { utils.err(it, node) }
      }
    } else {
      utils.err("@State should only be used on return types", node)
    }
  }

  private fun checkParameterAnnotation(node: AnnotationTree, annoMirror: AnnotationMirror, parent: Tree, parentParent: Tree, name: String) {
    if (parent is VariableTree && parentParent is MethodTree && parentParent.parameters.contains(parent)) {
      val typeMirror = TreeUtils.elementFromTree(parent)!!.asType()
      val graph = utils.classUtils.visitClassTypeMirror(typeMirror)
      if (graph == null) {
        utils.err("@$name has no meaning since this type has no protocol", node)
      } else {
        if (name == "Ensures" && !parent.modifiers.flags.contains(Modifier.FINAL)) {
          utils.err("Parameters with @Ensures should be final", node)
        }
        val stateNames = JTCUtils.getAnnotationValue(annoMirror)
        utils.checkStates(graph, stateNames).forEach { utils.err(it, node) }
      }
    } else {
      utils.err("@$name should only be used in method parameters", node)
    }
  }

  // Adapted from BaseTypeVisitor#checkPurity
  override fun visitMethod(node: MethodTree, p: Void?): Void? {
    super.visitMethod(node, p)

    val factory = checker.utils.factory
    val provider = factory.getProvider()

    if (!checker.getBooleanOption("checkPurityAnnotations", true)) {
      return null
    }

    val anyPurityAnnotation = PurityUtils.hasPurityAnnotation(provider, node)
    val suggestPureMethods = checker.getBooleanOption("suggestPureMethods")
    if (!anyPurityAnnotation && !suggestPureMethods) {
      return null
    }

    // check "no" purity
    val kinds = PurityUtils.getPurityKinds(provider, node)
    // @Deterministic makes no sense for a void method or constructor
    val isDeterministic = kinds.contains(Pure.Kind.DETERMINISTIC)
    if (isDeterministic) {
      if (TreeUtils.isConstructor(node)) {
        checker.reportWarning(node, "purity.deterministic.constructor")
      } else if (TreeUtils.typeOf(node.returnType).kind === TypeKind.VOID) {
        checker.reportWarning(node, "purity.deterministic.void.method")
      }
    }

    val body = factory.getPath(node.body)
    val r = if (body == null) {
      PurityResult()
    } else {
      PurityChecker.checkPurity(
        body,
        provider,
        checker.getBooleanOption("assumeSideEffectFree") || checker.getBooleanOption("assumePure"),
        checker.getBooleanOption("assumeDeterministic") || checker.getBooleanOption("assumePure"))
    }

    if (!r.isPure(kinds)) {
      reportPurityErrors(r, kinds)
    }

    if (suggestPureMethods && !isSynthetic(node)) {
      // Issue a warning if the method is pure, but not annotated as such.
      val additionalKinds = r.kinds.clone()
      additionalKinds.removeAll(kinds)
      if (TreeUtils.isConstructor(node)) {
        additionalKinds.remove(Pure.Kind.DETERMINISTIC)
      }
      if (!additionalKinds.isEmpty()) {
        when {
          additionalKinds.size == 2 -> checker.reportWarning(node, "purity.more.pure", node.name)
          additionalKinds.contains(Pure.Kind.SIDE_EFFECT_FREE) -> checker.reportWarning(node, "purity.more.sideeffectfree", node.name)
          additionalKinds.contains(Pure.Kind.DETERMINISTIC) -> checker.reportWarning(node, "purity.more.deterministic", node.name)
          else -> assert(false) { "CFVisitor reached undesirable state" }
        }
      }
    }
    return null
  }

  // Adapted from BaseTypeVisitor#reportPurityErrors
  private fun reportPurityErrors(result: PurityResult, expectedKinds: EnumSet<Pure.Kind>) {
    assert(!result.isPure(expectedKinds))
    val violations = EnumSet.copyOf(expectedKinds)
    violations.removeAll(result.kinds)
    if (violations.contains(Pure.Kind.DETERMINISTIC) || violations.contains(Pure.Kind.SIDE_EFFECT_FREE)) {
      val msgKeyPrefix = if (!violations.contains(Pure.Kind.SIDE_EFFECT_FREE)) {
        "purity.not.deterministic."
      } else if (!violations.contains(Pure.Kind.DETERMINISTIC)) {
        "purity.not.sideeffectfree."
      } else {
        "purity.not.deterministic.not.sideeffectfree."
      }
      for (r in result.notBothReasons) {
        reportPurityError(msgKeyPrefix, r)
      }
      if (violations.contains(Pure.Kind.SIDE_EFFECT_FREE)) {
        for (r in result.notSEFreeReasons) {
          reportPurityError("purity.not.sideeffectfree.", r)
        }
      }
      if (violations.contains(Pure.Kind.DETERMINISTIC)) {
        for (r in result.notDetReasons) {
          reportPurityError("purity.not.deterministic.", r)
        }
      }
    }
  }

  // Adapted from BaseTypeVisitor#reportPurityError
  private fun reportPurityError(msgKeyPrefix: String, r: Pair<Tree, String>) {
    val reason = r.second
    val msgKey = msgKeyPrefix + reason
    if (reason == "call") {
      if (r.first.kind === Tree.Kind.METHOD_INVOCATION) {
        val mitree = r.first as MethodInvocationTree
        checker.reportError(r.first, msgKey, mitree.methodSelect)
      } else {
        val nctree = r.first as NewClassTree
        checker.reportError(r.first, msgKey, nctree.identifier)
      }
    } else {
      checker.reportError(r.first, msgKey)
    }
  }

  // TODO replace later with TreeUtils.isSynthetic
  // Adapted from TreeUtils.isSynthetic
  private fun isSynthetic(ee: ExecutableElement): Boolean {
    val ms = ee as MethodSymbol
    val mod = ms.flags()
    return mod and (Flags.SYNTHETIC.toLong() or Flags.GENERATEDCONSTR) != 0L
  }

  // TODO replace later with TreeUtils.isSynthetic
  // Adapted from TreeUtils.isSynthetic
  private fun isSynthetic(node: MethodTree): Boolean {
    return isSynthetic(TreeUtils.elementFromDeclaration(node))
  }

}
