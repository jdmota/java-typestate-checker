package org.checkerframework.checker.jtc.utils

import com.sun.source.tree.ClassTree
import com.sun.source.tree.MethodTree
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
import javax.lang.model.element.Modifier
import javax.lang.model.type.DeclaredType
import javax.lang.model.type.TypeMirror

class ClassUtils(private val utils: JTCUtils) {

  private fun getGraph(protocolFilePath: Path, src: Element): Graph? {
    // Parse and process typestate
    val result = utils.processor.getGraph(protocolFilePath)
    result.error?.report(utils, src)
    return result.graph
  }

  private fun processTypestateAnnotation(sourceFilePath: Path, annotation: AnnotationMirror, src: Element): Graph? {
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
    val protocolFilePath = sourceFilePath.resolveSibling(file).normalize()
    // Parse and process typestate
    return getGraph(protocolFilePath, src)
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

      // Process
      val graph = classFile?.let { file -> // File where the class is
        getJTCTypestateAnnotation(sym.annotationMirrors)?.let {
          if (protocolFromConfig != null) {
            utils.err("Protocol for this class is also defined in the config file", sym)
          }
          processTypestateAnnotation(file, it, sym)
        }
      } ?: protocolFromConfig?.let { getGraph(it, sym) }

      // "computeIfAbsent" does not store null values, store an Optional instead
      Optional.ofNullable(graph?.let {
        TypestateProcessor.validateClassAndGraph(utils, sym, it)
      })
    }.orElse(null)
  }

  private val classNameToGraph = WeakIdentityHashMap<Symbol.ClassSymbol, Optional<Graph>>()

  companion object {
    fun getNonStaticPublicMethods(sym: Symbol.ClassSymbol) = sym.members().symbols.filterIsInstance(Symbol.MethodSymbol::class.java).filter {
      val flags = it.modifiers
      flags.contains(Modifier.PUBLIC) && !flags.contains(Modifier.STATIC)
    }

    fun getNonStaticMethodsWithBody(classTree: ClassTree) = classTree.members.filterIsInstance(MethodTree::class.java).filter {
      val flags = it.modifiers.flags
      it.body != null && !flags.contains(Modifier.STATIC) && !flags.contains(Modifier.ABSTRACT) && !flags.contains(Modifier.NATIVE)
    }

    fun getEnumLabels(classSymbol: Symbol.ClassSymbol) = classSymbol.members().symbols.filter { it.isEnum }.map { it.name.toString() }

    private fun isJavaLangObject(element: Element) = element is Symbol.ClassSymbol && element.qualifiedName.contentEquals("java.lang.Object")

    fun isJavaLangObject(type: TypeMirror) = if (type is DeclaredType) isJavaLangObject(type.asElement()) else false
  }

}
