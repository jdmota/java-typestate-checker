package org.checkerframework.checker.mungo;

import com.sun.source.tree.*;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.antlr.v4.runtime.tree.ParseTreeWalker;
import org.checkerframework.checker.mungo.typestate.TypestateBaseListener;
import org.checkerframework.checker.mungo.typestate.TypestateParser;
import org.checkerframework.checker.mungo.typestate.TypestateProcessor;
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

  private void parseTypestate(Path file, Tree annotation) {
    String filename = file.getFileName().toString();
    TypestateParser.Typestate_declarationContext tree;

    try {
      tree = TypestateProcessor.fromPath(file);
    } catch (IOException e) {
      error("Could not read file " + filename, annotation);
      return;
    } catch (ParseCancellationException exp) {
      error(TypestateProcessor.errorToString(filename, exp), annotation);
      return;
    }

    System.out.println(file);
    System.out.println(tree.getClass());

    TypestateBaseListener visitor = new TypestateBaseListener();
    ParseTreeWalker.DEFAULT.walk(visitor, tree);

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
    parseTypestate(protocolFilePath, tree);
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
}
