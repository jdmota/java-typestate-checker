package org.checkerframework.checker.mungo.internal;

import com.sun.source.tree.*;
import org.checkerframework.checker.mungo.qual.MungoState;
import org.checkerframework.checker.mungo.typestate.TypestateProcessor;
import org.checkerframework.checker.mungo.typestate.graph.Dot;
import org.checkerframework.checker.mungo.typestate.graph.Graph;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.source.Result;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.javacutil.TreeUtils;

import javax.lang.model.element.*;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

public class MungoTreeAnnotator extends TreeAnnotator {
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

  private Graph processMungoTypestateAnnotation(AnnotationTree annotation) {
    List<? extends ExpressionTree> args = annotation.getArguments();
    String file;
    try {
      ExpressionTree arg = args.get(0);
      ExpressionTree expr = ((AssignmentTree) arg).getExpression();
      Object value = ((LiteralTree) expr).getValue();
      file = (String) value;
    } catch (ClassCastException | IndexOutOfBoundsException exp) {
      err("Expected 1 string argument in @MungoTypestate", annotation);
      return null;
    }
    if (file.isEmpty()) {
      err("String in @MungoTypestate is empty", annotation);
      return null;
    }
    // Get the path of the file where the annotation is used
    Path sourceFilePath = Paths.get(atypeFactory.getVisitorState().getPath().getCompilationUnit().getSourceFile().toUri());
    // Get the path of the protocol file relative to the source file
    Path protocolFilePath = sourceFilePath.resolveSibling(file).normalize();

    // Parse and process typestate
    TypestateProcessor.GraphOrError result = processor.getGraph(protocolFilePath);

    if (result.error != null) {
      err(result.error.format(), annotation);
      return null;
    }

    // System.out.println(Dot.fromGraph(result.graph));
    return result.graph;
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
          // Process typestate
          Graph graph = processMungoTypestateAnnotation(anno);
          if (graph != null) {
            // Save info in the type of the class
            System.out.println("visitClass A " + annotatedTypeMirror);
            annotatedTypeMirror.replaceAnnotation(MungoUtils.createStateAnnotation(checker.getProcessingEnvironment(), graph.getStates()));
            System.out.println("visitClass B " + annotatedTypeMirror);
          }
        }
      }
    }

    return super.visitClass(node, annotatedTypeMirror);
  }

  @Override
  public Void visitNewClass(NewClassTree node, AnnotatedTypeMirror annotatedTypeMirror) {
    // Current type of new expression
    AnnotatedTypeMirror.AnnotatedDeclaredType type = (AnnotatedTypeMirror.AnnotatedDeclaredType) annotatedTypeMirror;
    // Type of the class
    AnnotatedTypeMirror.AnnotatedDeclaredType enclosingType = type.getEnclosingType();
    // Get @MungoState
    AnnotationMirror anno = enclosingType.getAnnotation(MungoState.class);
    System.out.println("visitNewClass A " + type);
    System.out.println("visitNewClass B " + enclosingType);
    if (anno != null) {
      annotatedTypeMirror.replaceAnnotation(anno);
    }
    System.out.println("visitNewClass C " + anno);
    System.out.println("visitNewClass D " + type);
    return super.visitNewClass(node, annotatedTypeMirror);
  }
}
