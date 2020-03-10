package org.checkerframework.checker.mungo.internal;

import org.checkerframework.checker.mungo.MungoAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFAbstractValue;
import org.checkerframework.javacutil.Pair;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import java.util.List;
import java.util.Set;

public class MungoAnalysis extends CFAbstractAnalysis<MungoValue, MungoStore, MungoTransfer> {

  public MungoAnalysis(BaseTypeChecker checker, MungoAnnotatedTypeFactory factory, List<Pair<VariableElement, MungoValue>> fieldValues) {
    super(checker, factory, fieldValues);
  }

  @Override
  public MungoStore createEmptyStore(boolean sequentialSemantics) {
    return new MungoStore(this, sequentialSemantics);
  }

  @Override
  public MungoStore createCopiedStore(MungoStore s) {
    return new MungoStore(s);
  }

  @Override
  public MungoValue createAbstractValue(Set<AnnotationMirror> annotations, TypeMirror underlyingType) {
    if (!CFAbstractValue.validateSet(annotations, underlyingType, qualifierHierarchy)) {
      return null;
    }
    return new MungoValue(this, annotations, underlyingType);
  }
}
