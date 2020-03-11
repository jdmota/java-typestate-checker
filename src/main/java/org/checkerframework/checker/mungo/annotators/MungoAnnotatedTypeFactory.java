package org.checkerframework.checker.mungo.annotators;

import org.checkerframework.checker.mungo.MungoChecker;
import org.checkerframework.checker.mungo.analysis.MungoAnalysis;
import org.checkerframework.checker.mungo.analysis.MungoStore;
import org.checkerframework.checker.mungo.analysis.MungoTransfer;
import org.checkerframework.checker.mungo.analysis.MungoValue;
import org.checkerframework.checker.mungo.qualifiers.MungoBottom;
import org.checkerframework.checker.mungo.qualifiers.MungoInfo;
import org.checkerframework.checker.mungo.qualifiers.MungoUnknown;
import org.checkerframework.checker.mungo.typecheck.MungoTypecheck;
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

  protected final AnnotationMirror BOTTOM_ANNO = AnnotationBuilder.fromClass(elements, MungoBottom.class);
  protected final AnnotationMirror INFO_ANNO = AnnotationBuilder.fromClass(elements, MungoInfo.class);
  protected final AnnotationMirror UNKNOWN_ANNO = AnnotationBuilder.fromClass(elements, MungoUnknown.class);

  public MungoAnnotatedTypeFactory(MungoChecker checker) {
    super(checker);
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
    return new ListTreeAnnotator(new MungoTreeAnnotator((MungoChecker) checker, this), super.createTreeAnnotator());
  }

  @Override
  protected DefaultQualifierForUseTypeAnnotator createDefaultForUseTypeAnnotator() {
    return new MungoDefaultQualifierForUseTypeAnnotator((MungoChecker) checker, this);
  }

  @Override
  protected Set<Class<? extends Annotation>> createSupportedTypeQualifiers() {
    Set<Class<? extends Annotation>> set = new HashSet<>();
    // Do NOT include @MungoTypestate here
    Collections.addAll(set, MungoBottom.class, MungoInfo.class, MungoUnknown.class);
    return set;
  }

  @Override
  public QualifierHierarchy createQualifierHierarchy(MultiGraphFactory factory) {
    return new MungoQualifierHierarchy(factory, BOTTOM_ANNO);
  }

  private final class MungoQualifierHierarchy extends GraphQualifierHierarchy {
    public MungoQualifierHierarchy(MultiGraphFactory f, AnnotationMirror bottom) {
      super(f, bottom);
    }

    // BOTTOM <: STATE <: UNKNOWN

    @Override
    public boolean isSubtype(AnnotationMirror subAnno, AnnotationMirror superAnno) {
      if (AnnotationUtils.areSameByName(subAnno, BOTTOM_ANNO)) {
        return true;
      }
      if (AnnotationUtils.areSameByName(subAnno, INFO_ANNO)) {
        if (AnnotationUtils.areSameByName(superAnno, INFO_ANNO)) {
          return MungoTypecheck.isSubType(subAnno, superAnno);
        }
        return AnnotationUtils.areSameByName(superAnno, UNKNOWN_ANNO);
      }
      if (AnnotationUtils.areSameByName(subAnno, UNKNOWN_ANNO)) {
        return AnnotationUtils.areSameByName(superAnno, UNKNOWN_ANNO);
      }
      return false;
    }
  }
}
