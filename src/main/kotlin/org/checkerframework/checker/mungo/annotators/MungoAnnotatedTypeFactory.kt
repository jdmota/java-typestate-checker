package org.checkerframework.checker.mungo.annotators

import com.sun.source.tree.*
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.checker.mungo.qualifiers.MungoBottom
import org.checkerframework.checker.mungo.qualifiers.MungoInternalInfo
import org.checkerframework.checker.mungo.qualifiers.MungoUnknown
import org.checkerframework.checker.mungo.typecheck.MungoBottomType
import org.checkerframework.checker.mungo.typecheck.MungoUnknownType
import org.checkerframework.checker.mungo.typestate.graph.State
import org.checkerframework.checker.mungo.utils.ClassUtils
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.dataflow.analysis.AnalysisResult
import org.checkerframework.dataflow.analysis.TransferResult
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.dataflow.cfg.node.Node
import org.checkerframework.dataflow.cfg.node.ReturnNode
import org.checkerframework.framework.flow.CFAbstractAnalysis
import org.checkerframework.framework.stub.StubTypes
import org.checkerframework.framework.type.*
import org.checkerframework.framework.util.DefaultAnnotationFormatter
import org.checkerframework.framework.util.GraphQualifierHierarchy
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy
import org.checkerframework.javacutil.*
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import java.util.*
import javax.lang.model.element.*

class MungoAnnotatedTypeFactory(checker: MungoChecker) : GenericAnnotatedTypeFactory<MungoValue, MungoStore, MungoTransfer, MungoAnalysis>(checker) {

  private val c = checker

  private val typesFromStubFilesField = StubTypes::class.java.getDeclaredField("typesFromStubFiles")
  private val typesFromStubFiles = mutableMapOf<Element, AnnotatedTypeMirror>()

  private val topAnnotation = MungoUnknownType.SINGLETON.buildAnnotation(checker.processingEnvironment)
  private val bottomAnnotation = MungoBottomType.SINGLETON.buildAnnotation(checker.processingEnvironment)

  private val typeApplier = MungoTypeApplier(c, this, topAnnotation, bottomAnnotation)

  init {
    typesFromStubFilesField.isAccessible = true
    postInit()
  }

  override fun postInit() {
    super.postInit()
    c.utils.setFactory(this)

    // Transform the @MungoState annotations for the proper @MungoInternalInfo ones
    val types = typesFromStubFilesField.get(stubTypes) as MutableMap<*, *>
    for ((element, annotatedType) in types) {
      typesFromStubFiles[element as Element] = annotatedType as AnnotatedTypeMirror
    }
    for ((_, annotatedType) in typesFromStubFiles) {
      typeApplier.fix(annotatedType)
    }
  }

  fun getCurrentRoot(): CompilationUnitTree = visitorState.path.compilationUnit

  // So that we get the original AnnotatedTypeMirror, with all the annotations
  // See "isSupportedQualifier" for context
  fun getTypeFromStub(elt: Element) = typesFromStubFiles[elt]

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
      if (MungoUtils.isMungoInternalAnnotation(am)) {
        val type = MungoUtils.mungoTypeFromAnnotation(am)
        sb.append(type.format())
      } else {
        super.formatAnnotationMirror(am, sb)
      }
    }
  }

  override fun addDefaultAnnotations(type: AnnotatedTypeMirror) {
    typeApplier.visit(type)
  }

  override fun addComputedTypeAnnotations(element: Element, type: AnnotatedTypeMirror) {
    typeApplier.visit(element, type)
  }

  override fun addComputedTypeAnnotations(tree: Tree, type: AnnotatedTypeMirror, iUseFlow: Boolean) {
    typeApplier.visit(tree, type)

    if (iUseFlow) {
      val value = getInferredValueFor(tree)
      if (value != null) {
        applyInferredAnnotations(type, value)
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

  override fun createSupportedTypeQualifiers(): Set<Class<out Annotation>> {
    // Do NOT include @MungoTypestate or @MungoState or @MungoNullable here
    return setOf(MungoBottom::class.java, MungoInternalInfo::class.java, MungoUnknown::class.java)
  }

  // Temporarily allow @MungoState annotations to be added to AnnotatedTypeMirror's
  // After postInit(), we transform the @MungoState annotations in the proper @MungoInternalInfo ones
  override fun isSupportedQualifier(a: AnnotationMirror?): Boolean {
    return a != null && (MungoUtils.isMungoInternalAnnotation(a) || (stubTypes.isParsing && MungoUtils.isMungoLibAnnotation(a)))
  }

  override fun createQualifierHierarchy(factory: MultiGraphQualifierHierarchy.MultiGraphFactory): QualifierHierarchy {
    return MungoQualifierHierarchy(factory, bottomAnnotation)
  }

  override fun createTypeHierarchy(): TypeHierarchy {
    return MungoTypeHierarchy(
      c,
      qualifierHierarchy,
      checker.getBooleanOption("ignoreRawTypeArguments", true),
      checker.hasOption("invariantArrays"))
  }

  private inner class MungoQualifierHierarchy(f: MultiGraphFactory, bottom: AnnotationMirror) : GraphQualifierHierarchy(f, bottom) {
    override fun findTops(supertypes: MutableMap<AnnotationMirror, MutableSet<AnnotationMirror>>?): MutableSet<AnnotationMirror> {
      return mutableSetOf(topAnnotation)
    }

    override fun findBottoms(supertypes: MutableMap<AnnotationMirror, MutableSet<AnnotationMirror>>?): MutableSet<AnnotationMirror> {
      return mutableSetOf(bottomAnnotation)
    }

    override fun getTopAnnotation(start: AnnotationMirror?): AnnotationMirror = topAnnotation

    override fun getBottomAnnotation(start: AnnotationMirror?): AnnotationMirror = bottomAnnotation

    override fun findAnnotationInHierarchy(annos: MutableCollection<out AnnotationMirror>, top: AnnotationMirror?): AnnotationMirror? {
      return annos.find { MungoUtils.isMungoInternalAnnotation(it) }
    }

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
    val methods = ClassUtils.getNonStaticMethodsWithBody(classTree).map { UnderlyingAST.CFGMethod(it, classTree) }

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
