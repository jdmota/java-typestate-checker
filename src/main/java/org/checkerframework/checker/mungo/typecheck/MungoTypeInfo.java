package org.checkerframework.checker.mungo.typecheck;

import org.checkerframework.checker.mungo.typestate.graph.Graph;
import org.checkerframework.checker.mungo.typestate.graph.states.State;

import javax.lang.model.element.*;
import javax.lang.model.type.DeclaredType;
import javax.lang.model.util.Elements;
import java.util.*;

public class MungoTypeInfo implements AnnotationMirror {

  public final Graph graph;
  public final Set<State> states;
  private final DeclaredType annotationType;
  private final Map<ExecutableElement, AnnotationValue> elementValues;

  private MungoTypeInfo(Graph graph, Set<State> states, DeclaredType at) {
    this.graph = graph;
    this.states = states;
    this.annotationType = at;
    this.elementValues = Collections.unmodifiableMap(Collections.emptyMap());
  }

  @Override
  public DeclaredType getAnnotationType() {
    return annotationType;
  }

  @Override
  public Map<? extends ExecutableElement, ? extends AnnotationValue> getElementValues() {
    return elementValues;
  }

  private static final String mungoInfoName = org.checkerframework.checker.mungo.qualifiers.MungoInfo.class.getCanonicalName(); // Cache name

  // Adapted from AnnotationBuilder.fromName
  public static MungoTypeInfo build(Elements elements, Graph graph, Set<State> states) {
    final TypeElement annoElt = elements.getTypeElement(mungoInfoName);
    if (annoElt == null || annoElt.getKind() != ElementKind.ANNOTATION_TYPE) {
      throw new AssertionError("MungoInfo.build");
    }
    final DeclaredType annoType = (DeclaredType) annoElt.asType();
    if (annoType == null) {
      throw new AssertionError("MungoInfo.build");
    }
    return new MungoTypeInfo(graph, states, annoType);
  }

}
