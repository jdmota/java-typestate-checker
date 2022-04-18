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

    for ((codeExpr, warnings) in inference1.warnings()) {
      val tree = inference2.getTree(codeExpr)
      val root = inference2.getRoot(codeExpr)
      checker.setCompilationRoot(root)
      for (warn in warnings) {
        checker.reportWarning(tree, warn)
      }
    }

    for ((codeExpr, errors) in inference1.errors()) {
      val tree = inference2.getTree(codeExpr)
      val root = inference2.getRoot(codeExpr)
      checker.setCompilationRoot(root)
      for (error in errors) {
        checker.reportError(tree, error)
      }
    }

    inference1.clearErrorsAndWarnings()
  }

  override fun visitAnnotation(node: AnnotationTree, p: Void?): Void? {
    val annoMirror = TreeUtils.annotationFromAnnotationTree(node)
    val parent = currentPath.parentPath.parentPath.leaf
    val parentParent = currentPath.parentPath.parentPath.parentPath.leaf
    val annotationName = AnnotationUtils.annotationName(annoMirror)

    when (annotationName) {
      JTCUtils.jtcRequiresAnno -> {
        if (checkRequires(node, parent, parentParent)) {
          checkParameterAnnotation(node, annoMirror, parent, "Requires")
        } else {
          utils.err("@Requires should only be used in method parameters", node)
        }
      }
      JTCUtils.jtcEnsuresAnno -> {
        when {
          checkEnsuresParam(node, parent, parentParent) -> checkParameterAnnotation(node, annoMirror, parent, "Ensures")
          checkEnsuresReturn(node, parent, parentParent) -> checkReturnTypeAnnotation(node, annoMirror, parent)
          else -> utils.err("@Ensures should only be used in method parameters or return types", node)
        }
      }
    }

    if (JTCUtils.typestateAnnotations.contains(annotationName)) {
      if (parent !is ClassTree || !parent.modifiers.annotations.contains(node)) {
        utils.err("@Typestate should go on classes or interfaces", node)
      }
    }

    return null
  }

  private fun checkRequires(node: AnnotationTree, parent: Tree, parentParent: Tree): Boolean {
    return parent is VariableTree && parentParent is MethodTree && parentParent.parameters.contains(parent)
  }

  private fun checkEnsuresParam(node: AnnotationTree, parent: Tree, parentParent: Tree): Boolean {
    return parent is VariableTree && parentParent is MethodTree && parentParent.parameters.contains(parent)
  }

  private fun checkEnsuresReturn(node: AnnotationTree, parent: Tree, parentParent: Tree): Boolean {
    return parent is MethodTree && parent.modifiers.annotations.contains(node)
  }

  private fun checkReturnTypeAnnotation(node: AnnotationTree, annoMirror: AnnotationMirror, parent: Tree) {
    val typeMirror = TreeUtils.elementFromTree((parent as MethodTree).returnType)!!.asType()
    val graph = utils.classUtils.getGraph(typeMirror)
    if (graph == null) {
      utils.err("@Ensures has no meaning since this type has no protocol", node)
    } else {
      val stateNames = JTCUtils.getAnnotationValue(annoMirror)
      utils.checkStates(graph, stateNames).forEach { utils.err(it, node) }
    }
  }

  private fun checkParameterAnnotation(node: AnnotationTree, annoMirror: AnnotationMirror, parent: Tree, name: String) {
    val typeMirror = TreeUtils.elementFromTree(parent as VariableTree)!!.asType()
    val graph = utils.classUtils.getGraph(typeMirror)
    if (graph == null) {
      utils.err("@$name has no meaning since this type has no protocol", node)
    } else {
      if (name == "Ensures" && !parent.modifiers.flags.contains(Modifier.FINAL)) {
        utils.err("Parameters with @Ensures should be final", node)
      }
      val stateNames = JTCUtils.getAnnotationValue(annoMirror)
      utils.checkStates(graph, stateNames).forEach { utils.err(it, node) }
    }
  }
}
