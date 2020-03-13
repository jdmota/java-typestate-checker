package org.checkerframework.checker.mungo.utils

import com.sun.source.tree.AnnotationTree
import com.sun.source.tree.AssignmentTree
import com.sun.source.tree.ClassTree
import com.sun.source.tree.LiteralTree
import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.mungo.lib.MungoTypestate
import org.checkerframework.checker.mungo.typecheck.MungoTypeInfo
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.com.google.common.collect.Sets
import org.checkerframework.javacutil.TreeUtils
import java.nio.file.Path
import java.nio.file.Paths
import javax.lang.model.element.Element
import javax.lang.model.element.TypeElement

class ClassUtils(private val utils: MungoUtils) {

  companion object {
    private val mungoTypestateName = MungoTypestate::class.java.canonicalName // Cache name
  }

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

  fun visitClassTree(sourceFilePath: Path, tree: ClassTree): MungoTypeInfo? {
    val modifiers = tree.modifiers
    val annotations = modifiers.annotations
    for (anno in annotations) {
      val elem = TreeUtils.elementFromTree(anno.annotationType)
      if (elem is TypeElement) {
        val name = elem.qualifiedName
        if (name.contentEquals(mungoTypestateName)) {
          // Process typestate
          val graph = processMungoTypestateAnnotation(sourceFilePath, anno)
          if (graph != null) {
            return MungoTypeInfo.build(utils.factory.elementUtils, graph, Sets.newHashSet(graph.getInitialState()))
          }
        }
      }
    }
    return null
  }

  fun visitClassSymbol(element: Element?): MungoTypeInfo? {
    if (element !is Symbol.ClassSymbol) {
      return null
    }
    // "getPath" may return null for java.lang.Object for example
    val path = utils.factory.treeUtils.getPath(element) ?: return null
    // Get the path of the file where the class is
    val sourceFilePath = Paths.get(path.compilationUnit.sourceFile.toUri())
    // Process class tree
    return visitClassTree(sourceFilePath, path.leaf as ClassTree)
  }

}
