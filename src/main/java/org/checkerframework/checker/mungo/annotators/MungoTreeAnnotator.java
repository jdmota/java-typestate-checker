package org.checkerframework.checker.mungo.annotators;

import com.sun.source.tree.ClassTree;
import com.sun.source.tree.NewClassTree;
import org.checkerframework.checker.mungo.MungoChecker;
import org.checkerframework.checker.mungo.qual.MungoInfo;
import org.checkerframework.checker.mungo.typecheck.MungoTypeInfo;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;

import java.nio.file.Paths;

public class MungoTreeAnnotator extends TreeAnnotator {
  private final MungoChecker checker;

  public MungoTreeAnnotator(MungoChecker checker, MungoAnnotatedTypeFactory atypeFactory) {
    super(atypeFactory);
    this.checker = checker;
  }

  @Override
  public Void visitNewClass(NewClassTree node, AnnotatedTypeMirror annotatedTypeMirror) {
    ClassTree tree = node.getClassBody();
    if (tree != null && !annotatedTypeMirror.hasAnnotation(MungoInfo.class)) {
      // Here we handle anonymous classes because doing this in MungoDefaultQualifierForUseTypeAnnotator is not enough
      // Extract information from class declaration so that the correct annotations can be applied to this instance
      MungoTypeInfo anno = checker.getUtils().visitClassTree(Paths.get(atypeFactory.getVisitorState().getPath().getCompilationUnit().getSourceFile().toUri()), tree);
      if (anno != null) {
        annotatedTypeMirror.replaceAnnotation(anno);
      }
    }
    return null;
  }
}
