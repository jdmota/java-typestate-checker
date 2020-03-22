package org.checkerframework.checker.mungo.annotators

import com.sun.tools.javac.code.Attribute
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.lib.MungoState
import org.checkerframework.checker.mungo.qualifiers.MungoInfo
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.framework.type.typeannotator.DefaultQualifierForUseTypeAnnotator
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.javacutil.ElementUtils
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.javacutil.TypesUtils
import java.nio.file.Paths
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element

class MungoDefaultQualifierForUseTypeAnnotator(private val checker: MungoChecker, typeFactory: MungoAnnotatedTypeFactory) : DefaultQualifierForUseTypeAnnotator(typeFactory) {
  // This is called by Checker when a reference to a class is encountered
  // to providing a variable with the default type information
  override fun getExplicitAnnos(element: Element): Set<AnnotationMirror> {
    // Extract information from class declaration
    val graph = checker.utils.visitClassSymbol(element)
    val set = super.getExplicitAnnos(element)
    if (graph != null) {
      val annotation = MungoUtils.buildAnnotation(checker.processingEnvironment, graph.file)
      val newSet: MutableSet<AnnotationMirror> = mutableSetOf(annotation)
      newSet.addAll(set)
      return newSet
    }
    return set
  }

  override fun visitDeclared(type: AnnotatedTypeMirror.AnnotatedDeclaredType, aVoid: Void?): Void? {
    val ret = super.visitDeclared(type, aVoid)
    val infoAnno = type.annotations.find { AnnotationUtils.areSameByClass(it, MungoInfo::class.java) }
    val stateAnno = type.underlyingType.annotationMirrors.find { AnnotationUtils.areSameByClass(it, MungoState::class.java) }
    if (infoAnno == null) {
      if (stateAnno != null) {
        // FIXME error location
        checker.utils.err("@MungoState has no meaning since this type has no protocol", type.underlyingType.asElement())
      }
    } else {
      if (stateAnno != null) {
        val file = AnnotationUtils.getElementValue(infoAnno, "file", String::class.java, false)
        val states = AnnotationUtils.getElementValueArray(stateAnno, "value", String::class.java, false)
        if (states != null) {
          val filePath = Paths.get(file)
          type.replaceAnnotation(MungoUtils.buildAnnotation(checker.processingEnvironment, filePath, states))
          // FIXME error location
          checker.utils.checkStates(filePath, states, type.underlyingType.asElement())
        }
      }
    }
    return ret
  }
}
