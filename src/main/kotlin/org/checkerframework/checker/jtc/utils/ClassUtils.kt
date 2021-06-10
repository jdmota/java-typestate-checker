package org.checkerframework.checker.jtc.utils

import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.jtc.typestate.TypestateProcessor
import org.checkerframework.checker.jtc.typestate.graph.Graph
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element
import javax.lang.model.type.DeclaredType
import javax.lang.model.type.TypeKind
import javax.lang.model.type.TypeMirror

class ClassUtils(private val utils: JTCUtils) {

  private val classNameToGraph = WeakIdentityHashMap<Symbol.ClassSymbol, Optional<Graph>>()

  private fun getGraph(protocolFilePath: Path, src: Element): Graph? {
    // Parse and process typestate
    val result = utils.processor.getGraph(protocolFilePath)
    result.error?.report(utils, src)
    return result.graph
  }

  private fun processTypestateAnnotation(sourceFilePath: Path, annotation: AnnotationMirror, src: Element): Path? {
    val args = annotation.elementValues.values
    val file = try {
      args.firstOrNull()?.value as String
    } catch (exp: ClassCastException) {
      utils.err("Expected 1 string argument in @Typestate", src)
      return null
    } catch (exp: IndexOutOfBoundsException) {
      utils.err("Expected 1 string argument in @Typestate", src)
      return null
    }
    if (file.isEmpty()) {
      utils.err("String in @Typestate is empty", src)
      return null
    }
    // Get the path of the protocol file relative to the source file
    return sourceFilePath.resolveSibling(file).normalize()
  }

  private fun getJTCTypestateAnnotation(annotationMirrors: Collection<AnnotationMirror>): AnnotationMirror? {
    return annotationMirrors.firstOrNull {
      JTCUtils.typestateAnnotations.contains(AnnotationUtils.annotationName(it))
    }
  }

  fun visitClassOfElement(element: Element): Graph? {
    // val type = utils.factory.fromElement(element) as? AnnotatedTypeMirror.AnnotatedDeclaredType ?: return null
    return visitClassTypeMirror(element.asType())
  }

  fun visitClassTypeMirror(type: TypeMirror): Graph? {
    return if (type is DeclaredType) visitClassSymbol(type.asElement()) else null
  }

  fun getSuperGraph(element: Symbol.ClassSymbol): Graph? {
    // TODO combine the union of the graphs instead of returning the first
    for (supertype in getSuperTypes(element)) {
      val graph = visitClassSymbol(supertype)
      if (graph != null) {
        return graph
      }
    }
    return null
  }

  fun visitClassSymbol(element: Element?): Graph? {
    if (element !is Symbol.ClassSymbol) return null
    return classNameToGraph.computeIfAbsent(element) { sym ->
      val qualifiedName = sym.qualifiedName.toString()
      val classFile = sym.sourcefile?.name?.let { Paths.get(it).toAbsolutePath() }
      val protocolFromConfig = utils.configUtils.getConfig().getProtocol(qualifiedName)

      utils.getTypeFromStub(sym)?.let {
        if (getJTCTypestateAnnotation(it.annotations) != null) {
          utils.err("@Typestate annotations in stub files are not supported. Use jtc.config instead", sym)
        }
      }

      val protocolFile = classFile?.let { file -> // File where the class is
        getJTCTypestateAnnotation(sym.annotationMirrors)?.let {
          if (protocolFromConfig != null) {
            utils.err("Protocol for this class is also defined in the config file", sym)
          }
          processTypestateAnnotation(file, it, sym)
        }
      } ?: protocolFromConfig

      val graph = protocolFile?.let { getGraph(protocolFile, sym) }?.let { TypestateProcessor.validateSubtyping(utils, sym, it) }
        ?: getSuperGraph(element)

      // "computeIfAbsent" does not store null values, store an Optional instead
      Optional.ofNullable(graph)
    }.orElse(null)
  }

  fun hasProtocol(type: TypeMirror): Boolean {
    return visitClassTypeMirror(type) != null
  }

  companion object {
    fun getSuperTypes(element: Symbol.ClassSymbol): List<Symbol.TypeSymbol> {
      val supertypes = mutableListOf(element.superclass.asElement())
      for (i in element.interfaces) {
        supertypes.add(i.asElement())
      }
      return supertypes
    }

    fun getEnumLabels(classSymbol: Symbol.ClassSymbol) = classSymbol.members().symbols.filter { it.isEnum }.map { it.name.toString() }

    private fun isJavaLangObject(element: Element) = element is Symbol.ClassSymbol && element.qualifiedName.contentEquals("java.lang.Object")

    fun isJavaLangObject(type: TypeMirror) = if (type is DeclaredType) isJavaLangObject(type.asElement()) else false
  }

}
