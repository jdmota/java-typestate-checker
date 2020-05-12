package org.checkerframework.checker.mungo.annotators

import com.sun.source.tree.*
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.checker.mungo.qualifiers.MungoBottom
import org.checkerframework.checker.mungo.qualifiers.MungoInternalInfo
import org.checkerframework.checker.mungo.qualifiers.MungoUnknown
import org.checkerframework.checker.mungo.typecheck.*
import org.checkerframework.checker.mungo.typestate.graph.State
import org.checkerframework.checker.mungo.utils.ClassUtils
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.checker.nullness.qual.Nullable
import org.checkerframework.dataflow.analysis.AnalysisResult
import org.checkerframework.dataflow.analysis.TransferResult
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.dataflow.cfg.node.Node
import org.checkerframework.dataflow.cfg.node.ReturnNode
import org.checkerframework.framework.flow.CFAbstractAnalysis
import org.checkerframework.framework.type.*
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator
import org.checkerframework.framework.type.treeannotator.TreeAnnotator
import org.checkerframework.framework.type.typeannotator.DefaultQualifierForUseTypeAnnotator
import org.checkerframework.framework.util.DefaultAnnotationFormatter
import org.checkerframework.framework.util.GraphQualifierHierarchy
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy
import org.checkerframework.javacutil.Pair
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import java.util.*
import javax.lang.model.element.*

class MungoAnnotatedTypeFactory(checker: MungoChecker) : GenericAnnotatedTypeFactory<MungoValue, MungoStore, MungoTransfer, MungoAnalysis>(checker) {

  private val c = checker
  val typeApplier = MungoTypeApplier(c)

  init {
    postInit()
  }

  fun getCurrentRoot(): CompilationUnitTree = visitorState.path.compilationUnit

  override fun createAnnotatedTypeFormatter(): AnnotatedTypeFormatter {
    val printVerboseGenerics = checker.hasOption("printVerboseGenerics")
    val defaultPrintInvisibleAnnos = printVerboseGenerics || checker.hasOption("printAllQualifiers")
    return DefaultAnnotatedTypeFormatter(
      MungoAnnotationFormatter(),
      printVerboseGenerics, // -AprintVerboseGenerics implies -AprintAllQualifiers
      defaultPrintInvisibleAnnos
    )
  }

  class MungoAnnotationFormatter : DefaultAnnotationFormatter() {
    override fun formatAnnotationMirror(am: AnnotationMirror, sb: StringBuilder) {
      if (MungoUtils.isMungoAnnotation(am)) {
        val type = MungoUtils.mungoTypeFromAnnotation(am)
        sb.append(type.format())
      } else {
        super.formatAnnotationMirror(am, sb)
      }
    }
  }

  override fun applyInferredAnnotations(type: AnnotatedTypeMirror, value: MungoValue) {
    // By setting omitSubtypingCheck to true, inferred information will always override the default type information
    val applier = DefaultInferredTypesApplier(true, qualifierHierarchy, this)
    applier.applyInferredType(type, value.annotations, value.underlyingType)
  }

  override fun getStoreAfter(node: Node): MungoStore? {
    return if (!analysis.isRunning) {
      // Fix assertion error "assert transferInput != null" on AnalysisResult#runAnalysisFor
      flowResult.getStoreAfter(node)
    } else {
      super.getStoreAfter(node)
    }
  }

  override fun createFlowAnalysis(fieldValues: List<Pair<VariableElement, MungoValue>>): MungoAnalysis {
    return MungoAnalysis(c, this, fieldValues)
  }

  override fun createFlowTransferFunction(analysis: CFAbstractAnalysis<MungoValue, MungoStore, MungoTransfer>): MungoTransfer {
    return MungoTransfer(c, analysis as MungoAnalysis)
  }

  override fun createTreeAnnotator(): TreeAnnotator {
    // TreeAnnotator that adds annotations to a type based on the contents of a tree
    return ListTreeAnnotator(MungoTreeAnnotator(c, this), super.createTreeAnnotator())
  }

  override fun createDefaultForUseTypeAnnotator(): DefaultQualifierForUseTypeAnnotator {
    return MungoDefaultQualifierForUseTypeAnnotator(c, this)
  }

  override fun createSupportedTypeQualifiers(): Set<Class<out Annotation>> {
    // Do NOT include @MungoTypestate or @MungoState or @MungoNullable here
    return setOf(MungoBottom::class.java, MungoInternalInfo::class.java, MungoUnknown::class.java)
  }

  override fun createQualifierHierarchy(factory: MultiGraphQualifierHierarchy.MultiGraphFactory): QualifierHierarchy {
    return MungoQualifierHierarchy(factory, MungoBottomType.SINGLETON.buildAnnotation(checker.processingEnvironment))
  }

  override fun createTypeHierarchy(): TypeHierarchy {
    return MungoTypeHierarchy(
      c,
      qualifierHierarchy,
      checker.getBooleanOption("ignoreRawTypeArguments", true),
      checker.hasOption("invariantArrays"))
  }

  private inner class MungoQualifierHierarchy(f: MultiGraphFactory, bottom: AnnotationMirror) : GraphQualifierHierarchy(f, bottom) {
    override fun isSubtype(subAnno: AnnotationMirror, superAnno: AnnotationMirror): Boolean {
      val sub = MungoUtils.mungoTypeFromAnnotation(subAnno)
      val sup = MungoUtils.mungoTypeFromAnnotation(superAnno)
      return sub.isSubtype(sup)
    }

    override fun leastUpperBound(a1: AnnotationMirror, a2: AnnotationMirror): AnnotationMirror {
      val type1 = MungoUtils.mungoTypeFromAnnotation(a1)
      val type2 = MungoUtils.mungoTypeFromAnnotation(a2)
      return type1.leastUpperBound(type2).buildAnnotation(checker.processingEnvironment)
    }

    override fun greatestLowerBound(a1: AnnotationMirror, a2: AnnotationMirror): AnnotationMirror {
      val type1 = MungoUtils.mungoTypeFromAnnotation(a1)
      val type2 = MungoUtils.mungoTypeFromAnnotation(a2)
      return type1.intersect(type2).buildAnnotation(checker.processingEnvironment)
    }
  }

  fun getTypeFor(tree: Tree, type: AnnotatedTypeMirror = getAnnotatedType(tree)) = getInferredValueFor(tree)?.info
    ?: getTypeFor(type)

  fun getTypeFor(type: AnnotatedTypeMirror) = MungoUtils.mungoTypeFromAnnotations(type.annotations)

  // This might be an hack, but is probably the best we can do now:
  // Intercept the analysis of a method in a class with protocol and redirect that processing to our own class analysis

  private val skipMethods = WeakIdentityHashMap<MethodTree, Boolean>()

  override fun analyze(
    queue: Queue<Pair<ClassTree, MungoStore?>>,
    lambdaQueue: Queue<Pair<LambdaExpressionTree, MungoStore?>>,
    ast: UnderlyingAST,
    fieldValues: List<Pair<VariableElement, MungoValue?>>,
    topClass: ClassTree, // This is the top class, not the one we read the members from
    isInitializationCode: Boolean,
    updateInitializationStore: Boolean,
    isStatic: Boolean,
    capturedStore: MungoStore?
  ) {
    // We are only interested in methods...
    if (ast !is UnderlyingAST.CFGMethod) {
      skipMethods.clear()
      super.analyze(queue, lambdaQueue, ast, fieldValues, topClass, isInitializationCode, updateInitializationStore, isStatic, capturedStore)
      return
    }

    // When we intercepted the first method, we already did the full class analysis
    // Time to ignore the methods.
    if (skipMethods.containsKey(ast.method)) {
      return
    }

    // Ignore static methods and take the time to fix an issue with Checker:
    // isStatic should be true
    // TODO make sure this is really an issue
    if (ast.method.modifiers.flags.contains(Modifier.STATIC)) {
      super.analyze(queue, lambdaQueue, ast, fieldValues, topClass, isInitializationCode, updateInitializationStore, true, capturedStore)
      return
    }

    val classTree = ast.classTree as JCTree.JCClassDecl
    val graph = c.utils.classUtils.visitClassSymbol(classTree.sym)

    // Repeat the logic in GenericAnnotatedTypeFactory#performFlowAnalysis to get all the relevant methods
    // And ignore static methods as well
    val methods = ClassUtils.getNonStaticMethods(classTree).map { UnderlyingAST.CFGMethod(it, classTree) }

    // Ignore all methods since we are now doing our own full analysis
    for (method in methods) {
      skipMethods[method.method] = true
    }

    // Split constructors from non-constructors, public and non-public
    val methodConstructors = methods.filter { TreeUtils.isConstructor(it.method) }
    val methodNonConstructors = methods.filterNot { TreeUtils.isConstructor(it.method) }
    val publicMethods = methodNonConstructors.filter { it.method.modifiers.flags.contains(Modifier.PUBLIC) }
    val nonPublicMethods = methodNonConstructors.filterNot { it.method.modifiers.flags.contains(Modifier.PUBLIC) }

    // Analyze constructors first
    for (method in methodConstructors) {
      super.analyze(queue, lambdaQueue, method, fieldValues, topClass, true, false, false, capturedStore)
    }

    // For the initial type information, just merge the exit stores of all the constructors
    // Even if a constructor calls another constructor, that should be fine.
    // Upon method invocations, CFAbstractStore#updateForMethodCall will invalidate previous information
    // In the worst case, all fields will be marked with unknown type...
    var initialStore = emptyStore
    for (method in methodConstructors) {
      val store = regularExitStores[method.method]
      if (store != null) {
        initialStore = initialStore.leastUpperBound(store)
      }
    }

    // Now analyze methods
    MungoClassAnalysis(c, this, analysis, transfer).analyzeClass(queue, lambdaQueue, root, classTree, publicMethods, nonPublicMethods, graph, initialStore)
  }

  // Mapping from state to store for classes with protocol
  private val classTreeToStatesToStore = mutableMapOf<ClassTree, Map<State, MungoStore>>()

  // Global upper bound store for classes without protocol
  private val classTreeToGlobalStore = mutableMapOf<ClassTree, MungoStore>()

  fun getStatesToStore(tree: ClassTree) = classTreeToStatesToStore[tree]

  fun getGlobalStore(tree: ClassTree) = classTreeToGlobalStore[tree]

  fun storeClassResult(classTree: ClassTree, stateToStore: Map<State, MungoStore>) {
    classTreeToStatesToStore[classTree] = stateToStore
  }

  fun storeClassResult(classTree: ClassTree, globalStore: MungoStore) {
    classTreeToGlobalStore[classTree] = globalStore
  }

  fun storeMethodResults(method: MethodTree, regularExitStore: MungoStore, returnStores: List<Pair<ReturnNode, TransferResult<MungoValue, MungoStore>?>>) {
    regularExitStores[method] = regularExitStore
    returnStatementStores[method] = returnStores
  }

  fun combineFlowResults(results: Iterable<AnalysisResult<MungoValue, MungoStore>>) {
    for (result in results) {
      flowResult.combine(result)
    }
  }

}
