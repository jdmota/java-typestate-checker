package jatyc.utils

import com.sun.tools.javac.code.Symbol
import jatyc.typestate.TypestateProcessor
import jatyc.typestate.graph.Graph
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element
import javax.lang.model.type.DeclaredType
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
    return getGraph(element.asType())
  }

  fun getGraph(type: TypeMirror): Graph? {
    return if (type is DeclaredType) visitClassSymbol(type.asElement()) else null
  }

  fun visitClassSymbol(element: Element?): Graph? {
    if (element !is Symbol.ClassSymbol) return null
    return classNameToGraph.computeIfAbsent(element) { sym ->
      val supers = utils.hierarchy.get(element.asType()).superTypes

      val qualifiedName = sym.qualifiedName.toString()
      val classFile = sym.sourcefile?.name?.let { Paths.get(it).toAbsolutePath() }
      val protocolFromConfig = utils.configUtils.getConfig().getProtocol(qualifiedName)

      utils.getTypeFromStub(sym)?.let {
        if (getJTCTypestateAnnotation(it.annotations) != null) {
          utils.err("@Typestate annotations in stub files are not supported. Use a config file instead", sym)
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

      val graph = protocolFile?.let { getGraph(protocolFile, sym) }?.let { TypestateProcessor.validateSubtyping(utils, sym, it, supers) }

      // "computeIfAbsent" does not store null values, store an Optional instead
      Optional.ofNullable(if (graph == null) {
        val superGraphs = supers.mapNotNull { it.getGraph() }.toSet()
        if (superGraphs.isNotEmpty()) {
          if (superGraphs.size == 1) {
            superGraphs.first()
          } else {
            utils.err("Multi-inheritance of protocols is not yet supported ($element)", sym)
            null
          }
        } else null
      } else graph)
    }.orElse(null)
  }

  fun hasProtocol(type: TypeMirror): Boolean {
    return getGraph(type) != null
  }
}
