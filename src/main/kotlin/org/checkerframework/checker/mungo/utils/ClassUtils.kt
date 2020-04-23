package org.checkerframework.checker.mungo.utils

import com.sun.source.tree.*
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.code.Type
import org.checkerframework.checker.mungo.typestate.TypestateProcessor
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element
import javax.lang.model.element.Modifier
import javax.lang.model.type.DeclaredType
import javax.lang.model.type.TypeMirror

class ClassUtils(private val utils: MungoUtils) {

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
    val protocolFilePath = sourceFilePath.toAbsolutePath().resolveSibling(file).normalize()
    // Parse and process typestate
    val result = utils.processor.getGraph(protocolFilePath)
    result.error?.let { utils.err(result.error.format(), src) }
    return result.graph
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
    // Get the path of the file where the class is
    val file = element.sourcefile?.name
    return if (file != null) {
      return classNameToGraph.computeIfAbsent(element) { sym ->
        getMungoTypestateAnnotation(sym.annotationMirrors)?.let {
          processMungoTypestateAnnotation(Paths.get(file), it, sym)
        }?.let {
          TypestateProcessor.validateClassAndGraph(utils, sym, it)
        }.let {
          // "computeIfAbsent" does not store null values, store an Optional instead
          Optional.ofNullable(it)
        }
      }.orElse(null)
    } else null
  }

  private val classNameToGraph = WeakIdentityHashMap<Symbol.ClassSymbol, Optional<Graph>>()

  companion object {
    fun getNonStaticMethods(sym: Symbol.ClassSymbol) = sym.members().symbols.filterIsInstance(Symbol.MethodSymbol::class.java).filter {
      val flags = it.modifiers
      !flags.contains(Modifier.STATIC) && !flags.contains(Modifier.ABSTRACT) && !flags.contains(Modifier.NATIVE)
    }

    fun getNonStaticPublicMethods(sym: Symbol.ClassSymbol) = getNonStaticMethods(sym).filter { it.modifiers.contains(Modifier.PUBLIC) }

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
