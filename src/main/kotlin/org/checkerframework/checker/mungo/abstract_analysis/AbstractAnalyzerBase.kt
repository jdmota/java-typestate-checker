package org.checkerframework.checker.mungo.abstract_analysis

import com.sun.source.tree.CompilationUnitTree
import com.sun.source.tree.Tree
import com.sun.source.tree.TypeCastTree
import com.sun.source.tree.VariableTree
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.TypeIntroducer
import org.checkerframework.checker.mungo.typecheck.MungoType
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.javacutil.ElementUtils
import org.checkerframework.javacutil.TreeUtils
import javax.lang.model.element.ElementKind
import javax.lang.model.element.ExecutableElement
import javax.lang.model.type.TypeMirror

abstract class AbstractAnalyzerBase(val checker: MungoChecker) {

  val utils get() = checker.utils
  val processingEnv = checker.processingEnvironment

  protected lateinit var root: JCTree.JCCompilationUnit
  protected lateinit var typeIntroducer: TypeIntroducer

  open fun setRoot(root: CompilationUnitTree) {
    this.root = root as JCTree.JCCompilationUnit
    this.typeIntroducer = TypeIntroducer(utils)
  }

  protected fun getInitialType(tree: Tree, type: AnnotatedTypeMirror): MungoType {
    if (tree is TypeCastTree) {
      return typeIntroducer.apply(type, typeIntroducer.declarationOpts)
    }
    val element = TreeUtils.elementFromTree(tree)
    // If it is a local variable...
    if (element?.kind == ElementKind.LOCAL_VARIABLE) {
      return typeIntroducer.apply(type, typeIntroducer.localDeclarationOpts)
    }
    // If it is a parameter...
    if (element?.kind == ElementKind.PARAMETER) {
      if (tree !is VariableTree) {
        // The tree refers to a parameter, but from inside the function.
        // Treat it like a local variable.
        return typeIntroducer.apply(type, typeIntroducer.localDeclarationOpts)
      }
      return typeIntroducer.apply(type, typeIntroducer.declarationOpts)
    }
    // If the return type has annotations or we are sure we have access to the method's code, refine
    if (element is ExecutableElement) {
      if (type.annotations.any { MungoUtils.isMungoLibAnnotation(it) } || !ElementUtils.isElementFromByteCode(element)) {
        return typeIntroducer.apply(type, typeIntroducer.declarationOpts)
      }
    }
    return typeIntroducer.apply(type, typeIntroducer.invalidated)
  }

  fun getInvalidated(type: TypeMirror): MungoType {
    val annotatedType = utils.factory.createType(type, false)
    annotatedType.addAnnotations(type.annotationMirrors)
    return typeIntroducer.get(annotatedType, typeIntroducer.invalidated)
  }
}
