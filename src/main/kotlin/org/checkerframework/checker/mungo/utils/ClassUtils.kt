package org.checkerframework.checker.mungo.utils

import com.sun.source.tree.AnnotationTree
import com.sun.source.tree.AssignmentTree
import com.sun.source.tree.ClassTree
import com.sun.source.tree.LiteralTree
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.javacutil.TreeUtils
import java.nio.file.Path
import java.nio.file.Paths
import javax.lang.model.element.Element
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

  companion object {
    fun getMungoTypestateAnnotation(tree: ClassTree): AnnotationTree? {
      val modifiers = tree.modifiers
      val annotations = modifiers.annotations
      for (anno in annotations) {
        val elem = TreeUtils.elementFromTree(anno.annotationType)
        if (elem is TypeElement) {
          val name = elem.qualifiedName
          if (name.contentEquals(MungoUtils.mungoTypestateName)) {
            return anno
          }
        }
      }
      return null
    }
  }

  fun visitClassTree(sourceFilePath: Path, tree: ClassTree): Graph? {
    return getMungoTypestateAnnotation(tree)?.let { processMungoTypestateAnnotation(sourceFilePath, it) }
  }

  fun visitClassTree(treePath: TreePath, tree: ClassTree): Graph? {
    // Get the path of the file where the class is
    val sourceFilePath = Paths.get(treePath.compilationUnit.sourceFile.toUri())
    return getMungoTypestateAnnotation(tree)?.let { processMungoTypestateAnnotation(sourceFilePath, it) }
  }

  fun visitClassSymbol(element: Element?): Graph? {
    if (element !is Symbol.ClassSymbol) {
      return null
    }
    // "getPath" may return null for java.lang.Object for example
    val path = utils.factory.treeUtils.getPath(element) ?: return null
    // Process class tree
    return visitClassTree(path, path.leaf as ClassTree)
  }

}
