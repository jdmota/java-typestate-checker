package org.checkerframework.checker.mungo.annotators

import com.sun.source.tree.*
import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.MungoAnalysis
import org.checkerframework.checker.mungo.analysis.MungoStore
import org.checkerframework.checker.mungo.analysis.MungoTransfer
import org.checkerframework.checker.mungo.analysis.MungoValue
import org.checkerframework.checker.mungo.qualifiers.MungoBottom
import org.checkerframework.checker.mungo.qualifiers.MungoInternalInfo
import org.checkerframework.checker.mungo.qualifiers.MungoUnknown
import org.checkerframework.checker.mungo.typecheck.*
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.checker.mungo.typestate.graph.states.AbstractState
import org.checkerframework.checker.mungo.typestate.graph.states.DecisionState
import org.checkerframework.checker.mungo.typestate.graph.states.State
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.dataflow.analysis.AnalysisResult
import org.checkerframework.dataflow.cfg.ControlFlowGraph
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.dataflow.cfg.node.Node
import org.checkerframework.framework.flow.CFAbstractAnalysis
import org.checkerframework.framework.flow.CFCFGBuilder
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory
import org.checkerframework.framework.type.QualifierHierarchy
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator
import org.checkerframework.framework.type.treeannotator.TreeAnnotator
import org.checkerframework.framework.type.typeannotator.DefaultQualifierForUseTypeAnnotator
import org.checkerframework.framework.util.GraphQualifierHierarchy
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.javacutil.Pair
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import java.util.*
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Modifier
import javax.lang.model.element.VariableElement
import kotlin.collections.LinkedHashSet

class MungoAnnotatedTypeFactory(checker: MungoChecker) : GenericAnnotatedTypeFactory<MungoValue, MungoStore, MungoTransfer, MungoAnalysis>(checker) {

  private val c = checker

  init {
    postInit()
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

  fun replaceWithInferredInfo(tree: Tree, type: AnnotatedTypeMirror) {
    val value = getInferredValueFor(tree)
    if (value != null) {
      type.replaceAnnotation(value.info.buildAnnotation(checker.processingEnvironment))
    }
  }

  // This is called in both MungoTreeAnnotator#visitVariable and MungoDefaultQualifierForUseTypeAnnotator#visitDeclared
  // For some reason, it must be called in "visitDeclared" as well...
  // Nonetheless, "visitVariable" is always called for both method arguments and variable declarations,
  // so we only report errors in that case, which provides "tree", for error location.
  fun visitMungoAnnotations(type: AnnotatedTypeMirror.AnnotatedDeclaredType, tree: Tree?) {
    val element = type.underlyingType.asElement()
    val stateAnno = type.underlyingType.annotationMirrors.find { AnnotationUtils.areSameByName(it, MungoUtils.mungoStateName) }
    val nullableAnno = type.underlyingType.annotationMirrors.find { AnnotationUtils.areSameByName(it, MungoUtils.mungoNullableName) }

    val stateTypes = run {
      val graph = c.utils.visitClassSymbol(element)
      if (graph == null) {
        if (stateAnno != null && tree != null) {
          c.utils.err("@MungoState has no meaning since this type has no protocol", tree)
        }
        MungoNoProtocolType.SINGLETON
      } else {
        val states = if (stateAnno == null) {
          graph.getAllConcreteStates()
        } else {
          val stateNames = AnnotationUtils.getElementValueArray(stateAnno, "value", String::class.java, false)
          if (tree != null) {
            c.utils.checkStates(graph.file, stateNames, tree)
          }
          graph.getAllConcreteStates().filter { stateNames.contains(it.name) }
        }
        MungoUnionType.create(states.map { MungoStateType.create(graph, it) })
      }
    }

    val maybeNullableType = if (nullableAnno == null) MungoBottomType.SINGLETON else MungoNullType.SINGLETON

    type.replaceAnnotation(MungoUnionType.create(listOf(stateTypes, maybeNullableType)).buildAnnotation(checker.processingEnvironment))
  }

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

    // ...in classes with protocol
    val graph = c.utils.visitClassTree(visitorState.path, ast.classTree)
    if (graph == null) {
      skipMethods.clear()
      super.analyze(queue, lambdaQueue, ast, fieldValues, topClass, isInitializationCode, updateInitializationStore, isStatic, capturedStore)
      return
    }

    // Ignore static methods as well and take the time to fix an issue with Checker:
    // isStatic should be true
    // TODO make sure this is really an issue
    if (ast.method.modifiers.flags.contains(Modifier.STATIC)) {
      super.analyze(queue, lambdaQueue, ast, fieldValues, topClass, isInitializationCode, updateInitializationStore, true, capturedStore)
      return
    }

    val classTree = ast.classTree

    // Repeat the logic in GenericAnnotatedTypeFactory#performFlowAnalysis to get all the relevant methods
    // And ignore static methods as well
    val methods = classTree.members.filterIsInstance(MethodTree::class.java).filter {
      val flags = it.modifiers.flags
      it.body != null && !flags.contains(Modifier.STATIC) && !flags.contains(Modifier.ABSTRACT) && !flags.contains(Modifier.NATIVE)
    }.map { UnderlyingAST.CFGMethod(it, classTree) }

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

    // Then analyze non-public methods
    for (method in nonPublicMethods) {
      super.analyze(queue, lambdaQueue, method, fieldValues, topClass, false, false, false, capturedStore)
    }

    // For the initial type information, just merge the exit stores of all the constructors
    // Even if a constructor calls another constructor, that should be fine.
    // Upon method invocations, CFAbstractStore#updateForMethodCall will invalidate previous information
    // In the worst case, all fields will be marked with unknown type...
    var initialStore = initializationStore ?: emptyStore
    for (method in methodConstructors) {
      val store = regularExitStores[method.method]
      if (store != null) {
        initialStore = initialStore.leastUpperBound(store)
      }
    }

    // Now analyze public methods keeping in mind the accepted method call orders in the protocol
    analyzeClass(queue, lambdaQueue, fieldValues, publicMethods, graph, initialStore)
  }

  // TODO infer method side-effects so that we do not just invalidate everything upon a method call...
  // TODO refactor this out

  private fun analyzeClass(
    classQueue: Queue<Pair<ClassTree, MungoStore?>>,
    lambdaQueue: Queue<Pair<LambdaExpressionTree, MungoStore?>>,
    fieldValues: List<Pair<VariableElement, MungoValue?>>,
    publicMethods: List<UnderlyingAST.CFGMethod>,
    graph: Graph,
    initialStore: MungoStore
  ) {
    val methodToCFG = mutableMapOf<MethodTree, ControlFlowGraph>()

    // Pre-work
    for (method in publicMethods) {
      val cfg = CFCFGBuilder.build(root, method, checker, this, processingEnv)
      methodToCFG[method.method] = cfg
      // TODO if (checker.hasOption("flowdotdir") || checker.hasOption("cfgviz")) handleCFGViz()
      // Add classes and lambdas declared in method
      for (cls in cfg.declaredClasses) classQueue.add(Pair.of(cls, getStoreBefore(cls)))
      for (lambda in cfg.declaredLambdas) lambdaQueue.add(Pair.of(lambda, getStoreBefore(lambda)))
    }

    val methodsWithTypes = publicMethods.map {
      Pair(it.method, TreeUtils.elementFromTree(it.method) as Symbol.MethodSymbol)
    }

    val currentClassPath = visitorState.path
    val methodToStatesCache = mutableMapOf<State, Map<MethodTree, AbstractState<*>>>()

    fun getMethodToState(state: State) = methodsWithTypes.mapNotNull { (method, symbol) ->
      val t = state.transitions.entries.find { c.utils.methodUtils.sameMethod(currentClassPath, symbol, it.key) }
      t?.value?.let { Pair(method, it) }
    }.toMap()

    val stateToStore = mutableMapOf<State, MungoStore>()
    val stateQueue = LinkedHashSet<State>()
    val results = mutableMapOf<MethodTree, AnalysisResult<MungoValue, MungoStore>>()

    fun maybeQueueState(state: State, store: MungoStore) {
      val currStore = stateToStore[state] ?: emptyStore
      val newStore = currStore.leastUpperBoundFields(store)
      if (currStore != newStore) {
        stateToStore[state] = newStore
        stateQueue.add(state)
      }
    }

    maybeQueueState(graph.getInitialState(), initialStore)

    while (stateQueue.isNotEmpty()) {
      val state = stateQueue.first()
      stateQueue.remove(state)

      val store = stateToStore[state]!!
      val methodToStates = methodToStatesCache.computeIfAbsent(state, ::getMethodToState)

      for ((method, destState) in methodToStates) {
        val cfg = methodToCFG[method]!!

        transfer.setFixedInitialStore(store)
        analysis.performAnalysis(cfg, fieldValues)

        val exitResult = analysis.getInput(cfg.regularExitBlock)!!
        val regularExitStore = exitResult.regularStore

        // Store/override result
        results[method] = analysis.result

        // Store/override exit and return statement stores
        regularExitStores[method] = regularExitStore
        returnStatementStores[method] = analysis.returnStatementStores

        // Merge new exit store with the stores of each destination state
        when (destState) {
          is State -> maybeQueueState(destState, regularExitStore)
          is DecisionState -> {
            // TODO handle enumeration values as well
            for ((label, dest) in destState.transitions) {
              when (label.label) {
                "true" -> maybeQueueState(dest, exitResult.thenStore)
                "false" -> maybeQueueState(dest, exitResult.elseStore)
                else -> maybeQueueState(dest, regularExitStore)
              }
            }
          }
        }
      }
    }

    // TODO ensure that if protocol completes, all objects inside also have its protocol completed

    // Finally, combine results into flowResult
    for ((_, result) in results) {
      flowResult.combine(result)
    }
  }

}
