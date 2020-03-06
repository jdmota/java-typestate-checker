package org.checkerframework.checker.mungo;

import com.sun.source.tree.*;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.checkerframework.checker.mungo.typestate.TypestateProcessor;
import org.checkerframework.checker.mungo.typestate.TypestateSyntaxError;
import org.checkerframework.checker.mungo.typestate.graph.Dot;
import org.checkerframework.checker.mungo.typestate.graph.Graph;
import org.checkerframework.checker.mungo.typestate.graph.exceptions.TypestateError;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.framework.source.Result;
import org.checkerframework.javacutil.TreeUtils;

import javax.lang.model.element.Element;
import javax.lang.model.element.Name;
import javax.lang.model.element.TypeElement;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

public class MungoVisitor extends BaseTypeVisitor<MungoAnnotatedTypeFactory> {
  public MungoVisitor(BaseTypeChecker checker) {
    super(checker);
  }

  private void error(String message, Tree where) {
    checker.report(Result.failure(message), where);
  }

  private void processTypestate(Path file, Tree annotation) {
    String filename = file.getFileName().toString();
    Graph graph;

    try {
      graph = TypestateProcessor.fromPath(file);
    } catch (IOException e) {
      error("Could not read file " + filename, annotation);
      return;
    } catch (ParseCancellationException exp) {
      error(TypestateSyntaxError.errorToString(filename, exp), annotation);
      return;
    } catch (TypestateError exp) {
      error(exp.getClass().toString(), annotation); // TODO
      return;
    }

    System.out.println(file);
    System.out.println(graph.getClass());
    System.out.println(graph.initialState);
    System.out.println(graph.endState);
    System.out.println(Dot.fromGraph(graph));
    // TODO
  }

  private void processMungoTypestateAnnotation(List<? extends ExpressionTree> args, Tree tree) {
    String file;
    try {
      ExpressionTree arg = args.get(0);
      ExpressionTree expr = ((AssignmentTree) arg).getExpression();
      Object value = ((LiteralTree) expr).getValue();
      file = (String) value;
    } catch (ClassCastException | IndexOutOfBoundsException exp) {
      error("Expected 1 string argument in @MungoTypestate", tree);
      return;
    }
    if (file.isEmpty()) {
      error("String in @MungoTypestate is empty", tree);
      return;
    }
    // Get the path of the file where the annotation is used
    Path sourceFilePath = Paths.get(getCurrentPath().getCompilationUnit().getSourceFile().toUri());
    // Get the path of the protocol file relative to the source file
    Path protocolFilePath = sourceFilePath.resolveSibling(file).normalize();
    // Parse and process typestate
    processTypestate(protocolFilePath, tree);
  }

  public void processClassTree(ClassTree classTree) {
    ModifiersTree modifiers = classTree.getModifiers();
    List<? extends AnnotationTree> annotations = modifiers.getAnnotations();

    for (AnnotationTree anno : annotations) {
      Element elem = TreeUtils.elementFromTree(anno.getAnnotationType());
      if (elem instanceof TypeElement) {
        Name name = ((TypeElement) elem).getQualifiedName();
        if (name.contentEquals("org.checkerframework.checker.mungo.MungoTypestate")) {
          processMungoTypestateAnnotation(anno.getArguments(), anno);
        }
      }
    }

    super.processClassTree(classTree);
  }

  // TODO visit all annotations to make sure @MungoTypestate only appears in class/interfaces??
  // TODO what if another class points to the same protocol file?? error? or fine? avoid duplicate processing
}
