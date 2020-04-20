package org.checkerframework.checker.mungo.annotators

import com.sun.source.tree.Tree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.typecheck.*
import org.checkerframework.checker.mungo.utils.ClassUtils
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.javacutil.TreeUtils
import javax.lang.model.element.Element

class MungoTypeApplier(private val c: MungoChecker) {

  fun apply(element: Element, type: AnnotatedTypeMirror.AnnotatedDeclaredType) {
    apply(element, null, type)
  }

  fun apply(tree: Tree, type: AnnotatedTypeMirror.AnnotatedDeclaredType) {
    apply(TreeUtils.elementFromTree(tree), tree, type)
  }

  fun apply(type: AnnotatedTypeMirror.AnnotatedDeclaredType) {
    apply(null, null, type)
  }

  private fun apply(element: Element?, tree: Tree?, type: AnnotatedTypeMirror.AnnotatedDeclaredType) {
    val stateAnno = type.underlyingType.annotationMirrors.find { AnnotationUtils.areSameByName(it, MungoUtils.mungoStateName) }
    val isNullable = type.underlyingType.annotationMirrors.any { MungoUtils.nullableAnnotations.contains(AnnotationUtils.annotationName(it)) }

    val considerAllPossible = element != null && element.kind.isField

    val types = run {
      if (ClassUtils.isJavaLangObject(type)) {
        if (stateAnno != null && tree != null) {
          c.utils.err("@MungoState has no meaning in Object type", tree)
        }
        MungoObjectType.SINGLETON
      } else {
        val graph = c.utils.classUtils.visitClassDeclaredType(type)
        if (graph == null) {
          if (stateAnno != null && tree != null) {
            c.utils.err("@MungoState has no meaning since this type has no protocol", tree)
          }
          MungoNoProtocolType.SINGLETON
        } else {
          if (considerAllPossible) {
            val states = graph.getAllConcreteStates()
            MungoUnionType.create(states.map { MungoStateType.create(graph, it) }.plus(MungoEndedType.SINGLETON).plus(MungoMovedType.SINGLETON))
          } else {
            val states = if (stateAnno == null) {
              graph.getAllConcreteStates()
            } else {
              val stateNames = AnnotationUtils.getElementValueArray(stateAnno, "value", String::class.java, false)
              if (tree != null) {
                c.utils.checkStates(graph.file, stateNames, tree)
              }
              graph.getAllConcreteStates().filter { stateNames.contains(it.name) }
            }
            MungoUnionType.create(states.map { MungoStateType.create(graph, it) })
          }
        }
      }
    }

    val maybeNullableType = if (isNullable) MungoNullType.SINGLETON else MungoBottomType.SINGLETON

    type.replaceAnnotation(MungoUnionType.create(listOf(types, maybeNullableType)).buildAnnotation(c.processingEnvironment))
  }

}
