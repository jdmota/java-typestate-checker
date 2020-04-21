package org.checkerframework.checker.mungo.utils

import com.sun.source.tree.*
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.code.Type
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.typestate.TypestateProcessor
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.javacutil.ElementUtils
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element
import javax.lang.model.element.Modifier
import javax.lang.model.element.TypeElement
import javax.lang.model.type.DeclaredType
import javax.lang.model.type.TypeMirror

class ClassUtils(private val utils: MungoUtils) {

  private fun processMungoTypestateAnnotation(sourceFilePath: Path, annotation: AnnotationTree, src: Tree): Graph? {
    val args = annotation.arguments
    val file = try {
      val arg = args[0]
      val expr = (arg as AssignmentTree).expression
      val value = (expr as LiteralTree).value
      value as String
    } catch (exp: ClassCastException) {
      utils.err("Expected 1 string argument in @MungoTypestate", src)
      return null
    } catch (exp: IndexOutOfBoundsException) {
      utils.err("Expected 1 string argument in @MungoTypestate", src)
      return null
    }
    if (file.isEmpty()) {
      utils.err("String in @MungoTypestate is empty", src)
      return null
    }
    // Get the path of the protocol file relative to the source file
    val protocolFilePath = sourceFilePath.resolveSibling(file).normalize()
    // Parse and process typestate
    val result = utils.processor.getGraph(protocolFilePath)
    result.error?.let { utils.err(result.error.format(), src) }
    return result.graph
  }

  private fun processMungoTypestateAnnotation(sourceFilePath: Path, annotation: AnnotationMirror, src: Element): Graph? {
    val args = annotation.elementValues.values
    val file = try {
      args.firstOrNull()?.value as String
    } catch (exp: ClassCastException) {
      utils.err("Expected 1 string argument in @MungoTypestate", src)
      return null
    } catch (exp: IndexOutOfBoundsException) {
      utils.err("Expected 1 string argument in @MungoTypestate", src)
      return null
    }
    if (file.isEmpty()) {
      utils.err("String in @MungoTypestate is empty", src)
      return null
    }
    // Get the path of the protocol file relative to the source file
    val protocolFilePath = sourceFilePath.resolveSibling(file).normalize()
    // Parse and process typestate
    val result = utils.processor.getGraph(protocolFilePath)
    result.error?.let { utils.err(result.error.format(), src) }
    return result.graph
  }

  private fun getMungoTypestateAnnotation(tree: JCTree.JCClassDecl): AnnotationTree? {
    val annotations = tree.modifiers.annotations.filter {
      val elem = TreeUtils.elementFromTree(it.annotationType)
      elem is TypeElement && MungoUtils.typestateAnnotations.contains(elem.qualifiedName.toString())
    }
    if (annotations.size > 1) {
      utils.err("There is more than 1 @MungoTypestate annotation", tree)
    }
    return annotations.firstOrNull()
  }

  private fun getMungoTypestateAnnotation(annotationMirrors: Collection<AnnotationMirror>): AnnotationMirror? {
    val annotations = annotationMirrors.filter {
      val elem = it.annotationType
      elem is Type && MungoUtils.typestateAnnotations.contains(elem.tsym.qualifiedName.toString())
    }
    return annotations.firstOrNull()
  }

  fun visitClassOfElement(element: Element): Graph? {
    val type = utils.factory.fromElement(element) as? AnnotatedTypeMirror.AnnotatedDeclaredType ?: return null
    return visitClassDeclaredType(type)
  }

  fun visitClassTypeMirror(type: TypeMirror): Graph? {
    return if (type is DeclaredType) visitClassSymbol(type.asElement()) else null
  }

  fun visitClassDeclaredType(type: AnnotatedTypeMirror.AnnotatedDeclaredType): Graph? {
    return visitClassSymbol(type.underlyingType.asElement())
  }

  fun visitClassSymbol(element: Element?): Graph? {
    if (element !is Symbol.ClassSymbol) {
      return null
    }
    val treePath = utils.factory.treeUtils.getPath(element)
    return if (treePath == null) {
      if (element.sourcefile != null) {
        // Workaround issue where ClassTree cannot be found in some instances...
        val sourceFilePath = Paths.get(element.sourcefile.name).toAbsolutePath()
        getMungoTypestateAnnotation(element.annotationMirrors)?.let {
          processMungoTypestateAnnotation(sourceFilePath, it, element)
        }
      } else null
    } else {
      visitClassTree(treePath)
    }
  }

  fun visitClassTree(treePath: TreePath): Graph? {
    return classTreeToGraph.computeIfAbsent(treePath.leaf as JCTree.JCClassDecl) { tree ->
      // Get the path of the file where the class is
      val sourceFilePath = Paths.get(treePath.compilationUnit.sourceFile.toUri())
      getMungoTypestateAnnotation(tree)?.let {
        processMungoTypestateAnnotation(sourceFilePath, it, tree)
      }?.let {
        TypestateProcessor.validateClassAndGraph(utils, tree, it)
      }.let {
        // "computeIfAbsent" does not store null values, store an Optional instead
        Optional.ofNullable(it)
      }
    }.orElse(null)
  }

  private val classTreeToGraph = WeakIdentityHashMap<JCTree.JCClassDecl, Optional<Graph>>()

  companion object {
    fun getNonStaticMethods(classTree: ClassTree) = classTree.members.filterIsInstance(MethodTree::class.java).filter {
      val flags = it.modifiers.flags
      it.body != null && !flags.contains(Modifier.STATIC) && !flags.contains(Modifier.ABSTRACT) && !flags.contains(Modifier.NATIVE)
    }

    fun getNonStaticPublicMethods(classTree: ClassTree) = getNonStaticMethods(classTree).filter { it.modifiers.flags.contains(Modifier.PUBLIC) }

    fun getEnumLabels(classSymbol: Symbol.ClassSymbol) = classSymbol.members().symbols.filter { it.isEnum }.map { it.name.toString() }

    fun isJavaLangObject(element: Element) = element is Symbol.ClassSymbol && element.qualifiedName.contentEquals("java.lang.Object")

    fun isJavaLangObject(type: TypeMirror) = if (type is DeclaredType) isJavaLangObject(type.asElement()) else false

    fun isJavaLangObject(type: AnnotatedTypeMirror.AnnotatedDeclaredType) = isJavaLangObject(type.underlyingType.asElement())
  }

}
