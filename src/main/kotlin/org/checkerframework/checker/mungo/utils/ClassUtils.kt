package org.checkerframework.checker.mungo.utils

import com.sun.source.tree.*
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.typestate.TypestateProcessor
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import java.nio.file.Path
import java.nio.file.Paths
import javax.lang.model.element.Element
import javax.lang.model.element.Modifier
import javax.lang.model.element.TypeElement

class ClassUtils(private val utils: MungoUtils) {

  private fun processMungoTypestateAnnotation(sourceFilePath: Path, annotation: AnnotationTree): Graph? {
    val args = annotation.arguments
    val file: String
    file = try {
      val arg = args[0]
      val expr = (arg as AssignmentTree).expression
      val value = (expr as LiteralTree).value
      value as String
    } catch (exp: ClassCastException) {
      utils.err("Expected 1 string argument in @MungoTypestate", annotation)
      return null
    } catch (exp: IndexOutOfBoundsException) {
      utils.err("Expected 1 string argument in @MungoTypestate", annotation)
      return null
    }
    if (file.isEmpty()) {
      utils.err("String in @MungoTypestate is empty", annotation)
      return null
    }
    // Get the path of the protocol file relative to the source file
    val protocolFilePath = sourceFilePath.resolveSibling(file).normalize()
    // Parse and process typestate
    val result = utils.processor.getGraph(protocolFilePath)
    if (result.error != null) {
      utils.err(result.error.format(), annotation)
      return null
    }
    return result.graph
  }

  private fun getMungoTypestateAnnotation(tree: JCTree.JCClassDecl): AnnotationTree? {
    val annotations = tree.modifiers.annotations.filter {
      val elem = TreeUtils.elementFromTree(it.annotationType)
      elem is TypeElement && elem.qualifiedName.contentEquals(MungoUtils.mungoTypestateName)
    }
    if (annotations.size > 1) {
      utils.err("There is more than 1 @MungoTypestate annotation", tree)
    }
    return annotations.firstOrNull()
  }

  fun visitClassOfElement(element: Element): Graph? {
    val type = utils.factory.fromElement(element) as? AnnotatedTypeMirror.AnnotatedDeclaredType ?: return null
    return visitClassDeclaredType(type)
  }

  fun visitClassDeclaredType(type: AnnotatedTypeMirror.AnnotatedDeclaredType): Graph? {
    return visitClassSymbol(type.underlyingType.asElement())
  }

  fun visitClassSymbol(element: Element?): Graph? {
    if (element !is Symbol.ClassSymbol) {
      return null
    }
    // "getPath" may return null for java.lang.Object for example
    val path = utils.factory.treeUtils.getPath(element) ?: return null
    // Process class tree
    return visitClassTree(path)
  }

  fun visitClassTree(treePath: TreePath): Graph? {
    return classTreeToGraph.computeIfAbsent(treePath.leaf as JCTree.JCClassDecl) { tree ->
      // Get the path of the file where the class is
      val sourceFilePath = Paths.get(treePath.compilationUnit.sourceFile.toUri())
      getMungoTypestateAnnotation(tree)?.let {
        processMungoTypestateAnnotation(sourceFilePath, it)
      }?.let {
        TypestateProcessor.validateClassAndGraph(utils, treePath, tree, it)
      }
    }
  }

  private val classTreeToGraph = WeakIdentityHashMap<JCTree.JCClassDecl, Graph?>()

  companion object {
    fun getNonStaticMethods(classTree: ClassTree) = classTree.members.filterIsInstance(MethodTree::class.java).filter {
      val flags = it.modifiers.flags
      it.body != null && !flags.contains(Modifier.STATIC) && !flags.contains(Modifier.ABSTRACT) && !flags.contains(Modifier.NATIVE)
    }

    fun getNonStaticPublicMethods(classTree: ClassTree) = getNonStaticMethods(classTree).filter { it.modifiers.flags.contains(Modifier.PUBLIC) }

    fun getEnumLabels(classSymbol: Symbol.ClassSymbol) = classSymbol.members().symbols.filter { it.isEnum }.map { it.name.toString() }

    fun isJavaLangObject(element: Element) = element is Symbol.ClassSymbol && element.qualifiedName.contentEquals("java.lang.Object")

    fun isJavaLangObject(type: AnnotatedTypeMirror.AnnotatedDeclaredType) = isJavaLangObject(type.underlyingType.asElement())
  }

}
