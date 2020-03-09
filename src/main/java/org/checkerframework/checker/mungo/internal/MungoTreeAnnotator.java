package org.checkerframework.checker.mungo.internal;

import com.sun.source.tree.*;
import org.checkerframework.checker.mungo.typestate.TypestateProcessor;
import org.checkerframework.checker.mungo.typestate.graph.Dot;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.source.Result;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.javacutil.TreeUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import javax.lang.model.element.Name;
import javax.lang.model.element.TypeElement;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Set;

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

    AnnotatedTypeFactory.ParameterizedExecutableType type = atypeFactory.constructorFromUse(node);
    Set<AnnotationMirror> annotations = type.executableType.getAnnotations();

    // TODO

    return super.visitNewClass(node, annotatedTypeMirror);
  }
}
