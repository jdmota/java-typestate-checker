package org.checkerframework.checker.mungo;

import org.checkerframework.checker.mungo.internal.*;
import org.checkerframework.checker.mungo.qual.MungoBottom;
import org.checkerframework.checker.mungo.qual.MungoState;
import org.checkerframework.checker.mungo.qual.MungoUnknown;
import org.checkerframework.checker.mungo.typestate.TypestateProcessor;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.type.typeannotator.DefaultQualifierForUseTypeAnnotator;
import org.checkerframework.framework.util.GraphQualifierHierarchy;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.Pair;

import static org.checkerframework.framework.util.MultiGraphQualifierHierarchy.MultiGraphFactory;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.VariableElement;
import java.lang.annotation.Annotation;
import java.util.*;

public class MungoAnnotatedTypeFactory extends GenericAnnotatedTypeFactory<MungoValue, MungoStore, MungoTransfer, MungoAnalysis> {

  protected final AnnotationMirror BOTTOM = AnnotationBuilder.fromClass(elements, MungoBottom.class);
  protected final AnnotationMirror STATE = AnnotationBuilder.fromClass(elements, MungoState.class);
  protected final AnnotationMirror UNKNOWN = AnnotationBuilder.fromClass(elements, MungoUnknown.class);

  public final MungoUtils utils;

  public MungoAnnotatedTypeFactory(BaseTypeChecker checker) {
    super(checker);
    TypestateProcessor processor = new TypestateProcessor();
    this.utils = new MungoUtils(checker, this, processor);
    this.postInit();
  }

  @Override
  protected MungoAnalysis createFlowAnalysis(List<Pair<VariableElement, MungoValue>> fieldValues) {
    return new MungoAnalysis(checker, this, fieldValues);
  }

  @Override
  public MungoTransfer createFlowTransferFunction(CFAbstractAnalysis<MungoValue, MungoStore, MungoTransfer> analysis) {
    return new MungoTransfer((MungoAnalysis) analysis);
  }

  @Override
  protected TreeAnnotator createTreeAnnotator() {
    // TreeAnnotator that adds annotations to a type based on the contents of a tree
    return new ListTreeAnnotator(new MungoTreeAnnotator(this), super.createTreeAnnotator());
  }

  /*@Override
  protected TypeAnnotator createTypeAnnotator() {
    // TypeAnnotator that adds annotations to a type based on the content of the type itself
    return new ListTypeAnnotator(new MungoTypeAnnotator(this), super.createTypeAnnotator());
  }*/

  @Override
  protected DefaultQualifierForUseTypeAnnotator createDefaultForUseTypeAnnotator() {
    return new MungoDefaultQualifierForUseTypeAnnotator(this);
  }

  @Override
  protected Set<Class<? extends Annotation>> createSupportedTypeQualifiers() {
    Set<Class<? extends Annotation>> set = new HashSet<>();
    // Do NOT include @MungoTypestate here
    Collections.addAll(set, MungoBottom.class, MungoState.class, MungoUnknown.class);
    return set;
  }

  @Override
  public QualifierHierarchy createQualifierHierarchy(MultiGraphFactory factory) {
    return new MungoQualifierHierarchy(factory, BOTTOM);
  }

  private final class MungoQualifierHierarchy extends GraphQualifierHierarchy {
    public MungoQualifierHierarchy(MultiGraphFactory f, AnnotationMirror bottom) {
      super(f, bottom);
    }

    // BOTTOM <: STATE <: UNKNOWN

    @Override
    public boolean isSubtype(AnnotationMirror subAnno, AnnotationMirror superAnno) {
      if (AnnotationUtils.areSameByName(subAnno, BOTTOM)) {
        return true;
      }
      if (AnnotationUtils.areSameByName(subAnno, STATE)) {
        if (AnnotationUtils.areSameByName(superAnno, STATE)) {
          Set<String> subStates = MungoUtils.getStatesFromAnno(subAnno);
          Set<String> superStates = MungoUtils.getStatesFromAnno(subAnno);
          return superStates.containsAll(subStates);
        }
        return AnnotationUtils.areSameByName(superAnno, UNKNOWN);
      }
      if (AnnotationUtils.areSameByName(subAnno, UNKNOWN)) {
        return AnnotationUtils.areSameByName(superAnno, UNKNOWN);
      }
      return false;
    }
  }
}
