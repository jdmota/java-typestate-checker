package org.checkerframework.checker.mungo.annotators

import com.sun.source.tree.Tree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.typecheck.*
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.framework.type.AnnotatedTypeMirror.*
import org.checkerframework.javacutil.TreeUtils
import java.util.*
import javax.lang.model.element.Element
import javax.lang.model.element.ElementKind

class MungoTypeApplier(private val c: MungoChecker) {

  private val typeVisitor = TypeVisitor(c, this)

  fun visit(tree: Tree, type: AnnotatedTypeMirror) {
    val element = TreeUtils.elementFromTree(tree)
    typeVisitor.visit(element, type)
  }

  fun visit(element: Element, type: AnnotatedTypeMirror) {
    typeVisitor.visit(element, type)
  }

  fun visit(type: AnnotatedTypeMirror) {
    typeVisitor.visit(null, type)
  }

  private fun apply(type: AnnotatedTypeMirror, refine: Boolean) {
    val mungoType = if (refine) {
      MungoTypecheck.typeDeclaration(c.utils, type.underlyingType)
    } else {
      MungoTypecheck.invalidate(c.utils, type.underlyingType)
    }
    type.replaceAnnotation(mungoType.buildAnnotation(c.processingEnvironment))
  }

  private fun shouldRefine(element: Element?): Boolean {
    return element?.kind == ElementKind.LOCAL_VARIABLE
  }

  // Adapted from org.checkerframework.framework.type.visitor.AnnotatedTypeScanner
  private class TypeVisitor(private val c: MungoChecker, private val typeApplier: MungoTypeApplier) {
    // To prevent infinite loops
    private val visitedNodes: MutableMap<AnnotatedTypeMirror, Void?> = IdentityHashMap()

    private fun reset() {
      visitedNodes.clear()
    }

    private fun visited(type: AnnotatedTypeMirror): Boolean {
      if (visitedNodes.containsKey(type)) return true
      visitedNodes[type] = null
      return false
    }

    private fun scan(element: Element?, type: AnnotatedTypeMirror, refine: Boolean) {
      when (type) {
        is AnnotatedDeclaredType -> {
          if (type.typeArguments.isNotEmpty()) {
            // Only declared types with type arguments might be recursive
            if (visited(type)) return
          }

          if (type.enclosingType != null) {
            scan(type.enclosingType)
          }
          scan(type.typeArguments)

          typeApplier.apply(type, refine || typeApplier.shouldRefine(element))
        }
        is AnnotatedArrayType -> {
          scan(type.componentType)
          typeApplier.apply(type, false)
        }
        is AnnotatedIntersectionType -> {
          if (visited(type)) return
          scan(type.directSuperTypes())
        }
        is AnnotatedUnionType -> {
          if (visited(type)) return
          scan(type.alternatives)
        }
        is AnnotatedExecutableType -> {
          val methodTree = c.treeUtils.getTree(type.element)

          scan(type.returnType, methodTree != null)
          if (type.receiverType != null) {
            scan(type.receiverType!!)
          }
          scan(type.parameterTypes, true)
          scan(type.thrownTypes)
          scan(type.typeVariables)
        }
        is AnnotatedTypeVariable -> {
          if (visited(type)) return

          scan(type.lowerBound)
          scan(type.upperBound)

          // Null type should not be the lower bound of type variables in generics
          // Avoiding type.argument.type.incompatible errors
          if (type.lowerBound is AnnotatedNullType) {
            type.lowerBound.replaceAnnotation(MungoBottomType.SINGLETON.buildAnnotation(c.processingEnvironment))
          }
        }
        is AnnotatedWildcardType -> {
          if (visited(type)) return
          scan(type.extendsBound)
          scan(type.superBound)
        }
        else -> typeApplier.apply(type, false)
      }
    }

    private fun scan(type: AnnotatedTypeMirror, refine: Boolean = false) {
      scan(null, type, refine)
    }

    private fun scan(types: Iterable<AnnotatedTypeMirror>, refine: Boolean = false) {
      for (type in types) {
        scan(type, refine)
      }
    }

    fun visit(element: Element?, type: AnnotatedTypeMirror) {
      reset()
      scan(element, type, false)
    }

  }

}
