package org.checkerframework.checker.mungo.annotators

import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.framework.type.*

class MungoTypeHierarchy(c: MungoChecker, qualifier: QualifierHierarchy, ignoreRawTypes: Boolean, invariantArrayComponents: Boolean) : DefaultTypeHierarchy(c, qualifier, ignoreRawTypes, invariantArrayComponents) {

  override fun createEqualityComparer(): StructuralEqualityComparer {
    return MungoEqualityComparer(typeargVisitHistory)
  }

  class MungoEqualityComparer(typeargVisitHistory: StructuralEqualityVisitHistory) : StructuralEqualityComparer(typeargVisitHistory) {
    override fun arePrimeAnnosEqual(type1: AnnotatedTypeMirror, type2: AnnotatedTypeMirror): Boolean {
      return super.arePrimeAnnosEqual(type1, type2) || run {
        val mungoType1 = MungoUtils.mungoTypeFromAnnotations(type1.annotations)
        val mungoType2 = MungoUtils.mungoTypeFromAnnotations(type2.annotations)
        mungoType1 == mungoType2
      }
    }
  }

}
