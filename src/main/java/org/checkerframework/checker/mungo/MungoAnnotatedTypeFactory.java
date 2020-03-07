package org.checkerframework.checker.mungo;

import com.sun.source.tree.*;
import org.checkerframework.checker.mungo.qual.MungoBottom;
import org.checkerframework.checker.mungo.qual.MungoState;
import org.checkerframework.checker.mungo.qual.MungoUnknown;
import org.checkerframework.checker.mungo.typestate.TypestateProcessor;
import org.checkerframework.checker.mungo.typestate.graph.Dot;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.source.Result;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.util.GraphQualifierHierarchy;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.TreeUtils;

import static org.checkerframework.framework.util.MultiGraphQualifierHierarchy.MultiGraphFactory;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import javax.lang.model.element.Name;
import javax.lang.model.element.TypeElement;
import java.lang.annotation.Annotation;
import java.nio.file.Path;
import java.nio.file.Paths;
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

  private static Set<String> getStateArg(AnnotationMirror anno) {
    return new HashSet<>(AnnotationUtils.getElementValueArray(anno, "value", String.class, false));
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
          Set<String> subStates = getStateArg(subAnno);
          Set<String> superStates = getStateArg(subAnno);
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

  private static class MungoTreeAnnotator extends TreeAnnotator {
    private final BaseTypeChecker checker;
    private final TypestateProcessor processor;

    public MungoTreeAnnotator(AnnotatedTypeFactory atypeFactory, BaseTypeChecker checker, TypestateProcessor processor) {
      super(atypeFactory);
      this.checker = checker;
      this.processor = processor;
    }

    private void err(String message, Tree where) {
      checker.report(Result.failure(message), where);
    }

    private void processMungoTypestateAnnotation(List<? extends ExpressionTree> args, Tree annotation) {
      String file;
      try {
        ExpressionTree arg = args.get(0);
        ExpressionTree expr = ((AssignmentTree) arg).getExpression();
        Object value = ((LiteralTree) expr).getValue();
        file = (String) value;
      } catch (ClassCastException | IndexOutOfBoundsException exp) {
        err("Expected 1 string argument in @MungoTypestate", annotation);
        return;
      }
      if (file.isEmpty()) {
        err("String in @MungoTypestate is empty", annotation);
        return;
      }
      // Get the path of the file where the annotation is used
      Path sourceFilePath = Paths.get(atypeFactory.getVisitorState().getPath().getCompilationUnit().getSourceFile().toUri());
      // Get the path of the protocol file relative to the source file
      Path protocolFilePath = sourceFilePath.resolveSibling(file).normalize();

      // Parse and process typestate
      TypestateProcessor.GraphOrError result = processor.getGraph(protocolFilePath);

      if (result.error == null) {
        System.out.println(Dot.fromGraph(result.graph));
      } else {
        err(result.error.format(), annotation);
      }
    }

    @Override
    public Void visitClass(ClassTree node, AnnotatedTypeMirror annotatedTypeMirror) {

      ModifiersTree modifiers = node.getModifiers();
      List<? extends AnnotationTree> annotations = modifiers.getAnnotations();

      for (AnnotationTree anno : annotations) {
        Element elem = TreeUtils.elementFromTree(anno.getAnnotationType());
        if (elem instanceof TypeElement) {
          Name name = ((TypeElement) elem).getQualifiedName();
          if (name.contentEquals("org.checkerframework.checker.mungo.qual.MungoTypestate")) {
            processMungoTypestateAnnotation(anno.getArguments(), anno);
          }
        }
      }

      return super.visitClass(node, annotatedTypeMirror);
    }

    @Override
    public Void visitNewClass(NewClassTree node, AnnotatedTypeMirror annotatedTypeMirror) {

      ParameterizedExecutableType type = atypeFactory.constructorFromUse(node);
      Set<AnnotationMirror> annotations = type.executableType.getAnnotations();

      // TODO

      return super.visitNewClass(node, annotatedTypeMirror);
    }
  }

}
