package jatyc.core.adapters

import com.sun.source.tree.*
import com.sun.tools.javac.tree.JCTree
import jatyc.JavaTypestateChecker
import jatyc.core.JavaTypesHierarchy
import jatyc.core.TypeIntroducer
import jatyc.core.TypecheckUtils
import jatyc.core.cfg.ClassDeclAndCompanion
import jatyc.core.linearmode.LinearModeClassAnalysis
import jatyc.utils.JTCUtils
import org.checkerframework.framework.source.SourceVisitor
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.javacutil.Pair
import org.checkerframework.javacutil.TreeUtils
import java.util.*
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Modifier

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

  override fun visitMethod(node: MethodTree, p: Void?): Void? {
    checkAnytimeAnnotations(node)
    return super.visitMethod(node, p)
  }

  private fun checkAnytimeAnnotations(method: MethodTree) {
    val annotations = method.modifiers.annotations.map { AnnotationUtils.annotationName(TreeUtils.annotationFromAnnotationTree(it)) }
    val hasAnytime = annotations.any { it == JTCUtils.jtcAnytimeAnno }
    val hasNotAnytime = annotations.any { it == JTCUtils.jtcNotAnytimeAnno }

    if (hasAnytime || hasNotAnytime) {
      val flags = method.modifiers.flags
      if (
        TreeUtils.isConstructor(method) ||
        flags.contains(Modifier.STATIC) ||
        flags.contains(Modifier.PROTECTED) ||
        flags.contains(Modifier.PRIVATE)
      ) {
        utils.err("@Anytime and @NotAnytime annotations do not apply to constructors/static/protected/private methods", method)
      } else if (hasAnytime && hasNotAnytime) {
        utils.err("@Anytime and @NotAnytime annotations should not be used in the same method", method)
      } else {
        val parent = currentPath.parentPath.leaf
        if (parent is JCTree.JCClassDecl) {
          val hasProtocol = utils.classUtils.hasProtocol(parent.type)
          if (hasAnytime && !hasProtocol) {
            utils.warn("Redundant use of @Anytime annotation in method of class without protocol", method)
          }
          if (hasNotAnytime && hasProtocol) {
            utils.warn("Redundant use of @NotAnytime annotation in method of class with protocol", method)
          }
        }
      }
    }
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
}
