package org.checkerframework.checker.mungo.utils;

import com.sun.source.tree.*;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.code.Symbol;
import org.checkerframework.checker.mungo.MungoChecker;
import org.checkerframework.checker.mungo.qual.MungoInfo;
import org.checkerframework.checker.mungo.qual.MungoTypestate;
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory;
import org.checkerframework.checker.mungo.typecheck.MungoTypeInfo;
import org.checkerframework.checker.mungo.typestate.TypestateProcessor;
import org.checkerframework.checker.mungo.typestate.graph.Graph;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.com.google.common.collect.Sets;
import org.checkerframework.framework.source.Result;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.TreeUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import javax.lang.model.element.Name;
import javax.lang.model.element.TypeElement;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;

public class MungoUtils {

  private static final String mungoInfoName = MungoInfo.class.getCanonicalName(); // Cache name
  private static final String mungoTypestateName = MungoTypestate.class.getCanonicalName(); // Cache name

  private final MungoChecker checker;
  private final MungoAnnotatedTypeFactory factory;
  private final TypestateProcessor processor;

  public MungoUtils(MungoChecker checker) {
    this.checker = checker;
    this.factory = (MungoAnnotatedTypeFactory) checker.getTypeFactory();
    this.processor = new TypestateProcessor();
  }

  public static @Nullable MungoTypeInfo getInfoFromAnnotations(Collection<AnnotationMirror> annotations) {
    for (AnnotationMirror annoMirror : annotations) {
      if (AnnotationUtils.areSameByName(annoMirror, mungoInfoName)) {
        return (MungoTypeInfo) annoMirror;
      }
    }
    return null;
  }

  public static MungoTypeInfo castAnnotation(AnnotationMirror annoMirror) {
    return (MungoTypeInfo) annoMirror;
  }

  public void err(String message, Tree where) {
    checker.report(Result.failure(message), where);
  }

  private @Nullable Graph processMungoTypestateAnnotation(Path sourceFilePath, AnnotationTree annotation) {
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
    // Get the path of the protocol file relative to the source file
    Path protocolFilePath = sourceFilePath.resolveSibling(file).normalize();
    // Parse and process typestate
    TypestateProcessor.GraphOrError result = processor.getGraph(protocolFilePath);

    if (result.error != null) {
      err(result.error.format(), annotation);
      return null;
    }

    return result.graph;
  }

  public @Nullable MungoTypeInfo visitClassTree(Path sourceFilePath, ClassTree tree) {
    ModifiersTree modifiers = tree.getModifiers();
    List<? extends AnnotationTree> annotations = modifiers.getAnnotations();

    for (AnnotationTree anno : annotations) {
      Element elem = TreeUtils.elementFromTree(anno.getAnnotationType());
      if (elem instanceof TypeElement) {
        Name name = ((TypeElement) elem).getQualifiedName();
        if (name.contentEquals(mungoTypestateName)) {
          // Process typestate
          Graph graph = processMungoTypestateAnnotation(sourceFilePath, anno);
          if (graph != null) {
            return MungoTypeInfo.build(factory.getElementUtils(), graph, Sets.newHashSet(graph.getInitialState()));
          }
        }
      }
    }

    return null;
  }

  public @Nullable MungoTypeInfo visitClassPath(TreePath path) {
    if (path == null) {
      // "path" may be null for java.lang.Object for example
      return null;
    }
    // Get the path of the file where the class is
    Path sourceFilePath = Paths.get(path.getCompilationUnit().getSourceFile().toUri());
    // Process class tree
    return visitClassTree(sourceFilePath, (ClassTree) path.getLeaf());
  }

  public @Nullable MungoTypeInfo visitClassSymbol(Element element) {
    if (!(element instanceof Symbol.ClassSymbol)) {
      return null;
    }
    TreePath path = factory.getTreeUtils().getPath(element);
    return visitClassPath(path);
  }

}
