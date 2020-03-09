package org.checkerframework.checker.mungo;

import org.checkerframework.checker.mungo.internal.MungoTreeAnnotator;
import org.checkerframework.checker.mungo.internal.MungoUtils;
import org.checkerframework.checker.mungo.qual.MungoBottom;
import org.checkerframework.checker.mungo.qual.MungoState;
import org.checkerframework.checker.mungo.qual.MungoUnknown;
import org.checkerframework.checker.mungo.typestate.TypestateProcessor;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.util.GraphQualifierHierarchy;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;

import static org.checkerframework.framework.util.MultiGraphQualifierHierarchy.MultiGraphFactory;

import javax.lang.model.element.AnnotationMirror;
import java.lang.annotation.Annotation;
import java.util.*;

public class MungoAnnotatedTypeFactory extends BaseAnnotatedTypeFactory {

  protected final AnnotationMirror BOTTOM = AnnotationBuilder.fromClass(elements, MungoBottom.class);
  protected final AnnotationMirror STATE = AnnotationBuilder.fromClass(elements, MungoState.class);
  protected final AnnotationMirror UNKNOWN = AnnotationBuilder.fromClass(elements, MungoUnknown.class);

  private final TypestateProcessor processor;

  public MungoAnnotatedTypeFactory(BaseTypeChecker checker) {
    super(checker);
    this.processor = new TypestateProcessor();
    this.postInit();
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

  @Override
  protected TreeAnnotator createTreeAnnotator() {
    return new ListTreeAnnotator(new MungoTreeAnnotator(this, checker, processor), super.createTreeAnnotator());
  }

}
