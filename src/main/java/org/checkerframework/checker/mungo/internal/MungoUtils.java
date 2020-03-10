package org.checkerframework.checker.mungo.internal;

import com.sun.source.tree.*;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.code.Symbol;
import org.checkerframework.checker.mungo.MungoAnnotatedTypeFactory;
import org.checkerframework.checker.mungo.qual.MungoState;
import org.checkerframework.checker.mungo.typestate.TypestateProcessor;
import org.checkerframework.checker.mungo.typestate.graph.Dot;
import org.checkerframework.checker.mungo.typestate.graph.Graph;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.source.Result;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.TreeUtils;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import javax.lang.model.element.Name;
import javax.lang.model.element.TypeElement;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class MungoUtils {

  private final MungoAnnotatedTypeFactory factory;
  private final BaseTypeChecker checker;
  private final TypestateProcessor processor;

  public MungoUtils(BaseTypeChecker checker, MungoAnnotatedTypeFactory factory, TypestateProcessor processor) {
    this.checker = checker;
    this.factory = factory;
    this.processor = processor;
  }

  public static AnnotationMirror createStateAnnotation(ProcessingEnvironment env, Set<String> states) {
    return createStateAnnotation(env, states.toArray(new String[]{}));
  }

  public static AnnotationMirror createStateAnnotation(ProcessingEnvironment env, String state) {
    return createStateAnnotation(env, new String[]{state});
  }

  public static AnnotationMirror createStateAnnotation(ProcessingEnvironment env, String[] states) {
    AnnotationBuilder builder = new AnnotationBuilder(env, MungoState.class);
    builder.setValue("value", states);
    return builder.build();
  }

  // "anno" is @MungoState
  public static Set<String> getStatesFromAnno(AnnotationMirror anno) {
    return new HashSet<>(AnnotationUtils.getElementValueArray(anno, "value", String.class, false));
  }

  private void err(String message, Tree where) {
    checker.report(Result.failure(message), where);
  }

  private Graph processMungoTypestateAnnotation(Path sourceFilePath, AnnotationTree annotation) {
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

    System.out.println(Dot.fromGraph(result.graph));
    return result.graph;
  }

  public AnnotationMirror visitClass(Path sourceFilePath, ClassTree tree) {
    ModifiersTree modifiers = tree.getModifiers();
    List<? extends AnnotationTree> annotations = modifiers.getAnnotations();

    for (AnnotationTree anno : annotations) {
      Element elem = TreeUtils.elementFromTree(anno.getAnnotationType());
      if (elem instanceof TypeElement) {
        Name name = ((TypeElement) elem).getQualifiedName();
        if (name.contentEquals("org.checkerframework.checker.mungo.qual.MungoTypestate")) {
          // Process typestate
          Graph graph = processMungoTypestateAnnotation(sourceFilePath, anno);
          if (graph != null) {
            return MungoUtils.createStateAnnotation(checker.getProcessingEnvironment(), graph.getFirstStateName());
          }
        }
      }
    }

    return null;
  }

  public AnnotationMirror visitClassSymbol(Element element) {
    if (!(element instanceof Symbol.ClassSymbol)) {
      return null;
    }
    TreePath path = factory.getTreeUtils().getPath(element);
    if (path == null) {
      // "path" may be null for java.lang.Object for example
      return null;
    }
    // Get the path of the file where the class is
    Path sourceFilePath = Paths.get(path.getCompilationUnit().getSourceFile().toUri());
    // Process class tree
    return visitClass(sourceFilePath, (ClassTree) path.getLeaf());
  }

}
