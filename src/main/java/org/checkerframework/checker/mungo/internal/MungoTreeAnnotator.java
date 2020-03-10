package org.checkerframework.checker.mungo.internal;

import com.sun.source.tree.ClassTree;
import com.sun.source.tree.NewClassTree;
import org.checkerframework.checker.mungo.MungoAnnotatedTypeFactory;
import org.checkerframework.checker.mungo.qual.MungoState;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;

import javax.lang.model.element.AnnotationMirror;
import java.nio.file.Paths;

public class MungoTreeAnnotator extends TreeAnnotator {
  private final MungoUtils utils;

  public MungoTreeAnnotator(MungoAnnotatedTypeFactory atypeFactory) {
    super(atypeFactory);
    this.utils = atypeFactory.utils;
  }

  @Override
  public Void visitNewClass(NewClassTree node, AnnotatedTypeMirror annotatedTypeMirror) {
    ClassTree tree = node.getClassBody();
    if (tree != null && !annotatedTypeMirror.hasAnnotation(MungoState.class)) {
      // Here we handle anonymous classes because doing this in MungoDefaultQualifierForUseTypeAnnotator is not enough
      // Extract information from class declaration so that the correct annotations can be applied to this instance
      AnnotationMirror anno = utils.visitClassTree(Paths.get(atypeFactory.getVisitorState().getPath().getCompilationUnit().getSourceFile().toUri()), tree);
      if (anno != null) {
        annotatedTypeMirror.replaceAnnotation(anno);
      }
    }
    return null;
  }
}
