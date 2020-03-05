package org.checkerframework.checker.mungo;

import com.sun.source.tree.*;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.framework.source.Result;
import org.checkerframework.javacutil.TreeUtils;

import javax.lang.model.element.Element;
import javax.lang.model.element.Name;
import javax.lang.model.element.TypeElement;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

public class MungoVisitor extends BaseTypeVisitor<MungoAnnotatedTypeFactory> {
  public MungoVisitor(BaseTypeChecker checker) {
    super(checker);
  }

  private void processMungoTypestateAnnotation(List<? extends ExpressionTree> args, Tree tree) {
    String file;
    try {
      ExpressionTree arg = args.get(0);
      ExpressionTree expr = ((AssignmentTree) arg).getExpression();
      Object value = ((LiteralTree) expr).getValue();
      file = (String) value;
    } catch (ClassCastException | IndexOutOfBoundsException exp) {
      checker.report(Result.failure("Expected 1 string argument in @MungoTypestate"), tree);
      return;
    }
    if (file.isEmpty()) {
      checker.report(Result.failure("String in @MungoTypestate is empty"), tree);
      return;
    }
    // Get the path of the file where the annotation is used
    Path sourceFilePath = Paths.get(getCurrentPath().getCompilationUnit().getSourceFile().toUri());
    // Get the path of the protocol file relative to the source file
    Path protocolFilePath = sourceFilePath.resolveSibling(file).normalize();
    // TODO
    System.out.println(protocolFilePath);
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
