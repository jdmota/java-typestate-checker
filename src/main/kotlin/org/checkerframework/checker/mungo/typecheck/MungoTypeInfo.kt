package org.checkerframework.checker.mungo.typecheck

import org.checkerframework.checker.mungo.qualifiers.MungoInfo
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.checker.mungo.typestate.graph.states.State
import java.util.*
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.AnnotationValue
import javax.lang.model.element.ElementKind
import javax.lang.model.element.ExecutableElement
import javax.lang.model.type.DeclaredType
import javax.lang.model.util.Elements

// Type information contains a set of possible states
// And the graph where those states belong
class MungoTypeInfo private constructor(val graph: Graph, val states: Set<State>, private val annotationType: DeclaredType) : AnnotationMirror {
  private val elementValues: Map<ExecutableElement, AnnotationValue> = Collections.unmodifiableMap(emptyMap())

  override fun getAnnotationType(): DeclaredType {
    return annotationType
  }

  override fun getElementValues(): Map<out ExecutableElement, AnnotationValue> {
    return elementValues
  }

  companion object {
    private val mungoInfoName = MungoInfo::class.java.canonicalName // Cache name

    // Adapted from AnnotationBuilder.fromName
    fun build(elements: Elements, graph: Graph, states: Set<State>): MungoTypeInfo {
      val annoElt = elements.getTypeElement(mungoInfoName)
      if (annoElt == null || annoElt.kind != ElementKind.ANNOTATION_TYPE) {
        throw AssertionError("MungoInfo.build")
      }
      val annoType = annoElt.asType() as DeclaredType
      return MungoTypeInfo(graph, states, annoType)
    }
  }

}
