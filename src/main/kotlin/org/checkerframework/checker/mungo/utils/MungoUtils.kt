package org.checkerframework.checker.mungo.utils

import com.sun.source.tree.*
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol.ClassSymbol
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory
import org.checkerframework.checker.mungo.lib.MungoTypestate
import org.checkerframework.checker.mungo.qualifiers.MungoInfo
import org.checkerframework.checker.mungo.typecheck.MungoTypeInfo
import org.checkerframework.checker.mungo.typestate.TypestateProcessor
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.com.google.common.collect.Sets
import org.checkerframework.framework.source.Result
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.javacutil.TreeUtils
import java.nio.file.Path
import java.nio.file.Paths
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element
import javax.lang.model.element.TypeElement

class MungoUtils(private val checker: MungoChecker) {

  private val factory: MungoAnnotatedTypeFactory = checker.typeFactory as MungoAnnotatedTypeFactory
  private val processor: TypestateProcessor = TypestateProcessor()

  fun err(message: String, where: Tree?) {
    checker.report(Result.failure(message), where)
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
      err("Expected 1 string argument in @MungoTypestate", annotation)
      return null
    } catch (exp: IndexOutOfBoundsException) {
      err("Expected 1 string argument in @MungoTypestate", annotation)
      return null
    }
    if (file.isEmpty()) {
      err("String in @MungoTypestate is empty", annotation)
      return null
    }
    // Get the path of the protocol file relative to the source file
    val protocolFilePath = sourceFilePath.resolveSibling(file).normalize()
    // Parse and process typestate
    val result = processor.getGraph(protocolFilePath)
    if (result.error != null) {
      err(result.error.format(), annotation)
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
            return MungoTypeInfo.build(factory.elementUtils, graph, Sets.newHashSet(graph.getInitialState()))
          }
        }
      }
    }
    return null
  }

  fun visitClassPath(path: TreePath?): MungoTypeInfo? {
    if (path == null) {
      // "path" may be null for java.lang.Object for example
      return null
    }
    // Get the path of the file where the class is
    val sourceFilePath = Paths.get(path.compilationUnit.sourceFile.toUri())
    // Process class tree
    return visitClassTree(sourceFilePath, path.leaf as ClassTree)
  }

  fun visitClassSymbol(element: Element?): MungoTypeInfo? {
    if (element !is ClassSymbol) {
      return null
    }
    val path = factory.treeUtils.getPath(element)
    return visitClassPath(path)
  }

  companion object {
    private val mungoInfoName = MungoInfo::class.java.canonicalName // Cache name
    private val mungoTypestateName = MungoTypestate::class.java.canonicalName // Cache name

    fun getInfoFromAnnotations(annotations: Collection<AnnotationMirror?>): MungoTypeInfo? {
      for (annoMirror in annotations) {
        if (AnnotationUtils.areSameByName(annoMirror, mungoInfoName)) {
          return annoMirror as MungoTypeInfo?
        }
      }
      return null
    }

    fun castAnnotation(annoMirror: AnnotationMirror): MungoTypeInfo {
      return annoMirror as MungoTypeInfo
    }
  }

}
