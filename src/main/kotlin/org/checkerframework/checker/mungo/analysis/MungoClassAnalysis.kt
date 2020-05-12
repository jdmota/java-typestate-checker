package org.checkerframework.checker.mungo.analysis

import com.sun.source.tree.ClassTree
import com.sun.source.tree.CompilationUnitTree
import com.sun.source.tree.LambdaExpressionTree
import com.sun.source.tree.MethodTree
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory
import org.checkerframework.checker.mungo.typestate.graph.AbstractState
import org.checkerframework.checker.mungo.typestate.graph.DecisionState
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.checker.mungo.typestate.graph.State
import org.checkerframework.dataflow.analysis.AnalysisResult
import org.checkerframework.dataflow.analysis.TransferInput
import org.checkerframework.dataflow.cfg.ControlFlowGraph
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.dataflow.cfg.node.BooleanLiteralNode
import org.checkerframework.dataflow.cfg.node.ReturnNode
import org.checkerframework.framework.flow.CFCFGBuilder
import org.checkerframework.javacutil.TreeUtils
import java.util.*
import kotlin.collections.LinkedHashSet

class MungoClassAnalysis(
  private val c: MungoChecker,
  private val f: MungoAnnotatedTypeFactory,
  private val a: MungoAnalysis,
  private val t: MungoTransfer
) {

  // The results for each method to be merged later.
  private val results = mutableMapOf<MethodTree, AnalysisResult<MungoValue, MungoStore>>()

  // Method to CFG
  private val methodToCFG = mutableMapOf<MethodTree, ControlFlowGraph>()

  fun analyzeClass(
    classQueue: Queue<org.checkerframework.javacutil.Pair<ClassTree, MungoStore?>>,
    lambdaQueue: Queue<org.checkerframework.javacutil.Pair<LambdaExpressionTree, MungoStore?>>,
    root: CompilationUnitTree?,
    classTree: JCTree.JCClassDecl,
    publicMethods: List<UnderlyingAST.CFGMethod>,
    nonPublicMethods: List<UnderlyingAST.CFGMethod>,
    graph: Graph?,
    initialStore: MungoStore
  ) {
    fun prepare(method: UnderlyingAST.CFGMethod) {
      val cfg = CFCFGBuilder.build(root, method, c, f, c.processingEnvironment)
      methodToCFG[method.method] = cfg
      // TODO if (checker.hasOption("flowdotdir") || checker.hasOption("cfgviz")) handleCFGViz()
      // Add classes and lambdas declared in method
      for (cls in cfg.declaredClasses) classQueue.add(org.checkerframework.javacutil.Pair.of(cls, f.getStoreBefore(cls)))
      for (lambda in cfg.declaredLambdas) lambdaQueue.add(org.checkerframework.javacutil.Pair.of(lambda, f.getStoreBefore(lambda)))
    }

    // Pre-work
    for (method in publicMethods) prepare(method)
    for (method in nonPublicMethods) prepare(method)

    // Analyze non public methods
    // TODO improve this by using the upper bound of the stores of all public methods, instead of invalidating everything
    val entryStore = initialStore.invalidateAllFields()
    for (method in nonPublicMethods) {
      analyze(entryStore, method.method)
    }

    // Analyze public methods

    a.inPublicMethodAnalysis = true

    if (graph == null) {
      analyzeClassWithoutProtocol(classTree, publicMethods, initialStore)
    } else {
      analyzeClassWithProtocol(classTree, publicMethods, graph, initialStore)
    }

    a.inPublicMethodAnalysis = false
  }

  private fun analyzeClassWithProtocol(
    classTree: JCTree.JCClassDecl,
    publicMethods: List<UnderlyingAST.CFGMethod>,
    graph: Graph,
    initialStore: MungoStore
  ) {
    val methodsWithTypes = publicMethods.map {
      Pair(it.method, TreeUtils.elementFromTree(it.method) as Symbol.MethodSymbol)
    }

    val methodToStatesCache = mutableMapOf<State, Map<MethodTree, AbstractState<*>>>()
    val env = graph.getEnv()

    fun getMethodToState(state: State) = run {
      methodsWithTypes.mapNotNull { (method, symbol) ->
        val t = state.transitions.entries.find { c.utils.methodUtils.sameMethod(env, symbol, it.key) }
        t?.value?.let { Pair(method, it) }
      }.toMap()
    }

    // States lead us to methods that may be called. So we need information about each state.
    val stateToStore = mutableMapOf<State, MungoStore>()
    // But since the same method may be available from different states,
    // we also need to store the entry store for each method.
    val methodToStore = mutableMapOf<MethodTree, MungoStore>()
    // States that need recomputing. Use a LinkedHashSet to keep some order and avoid duplicates.
    val stateQueue = LinkedHashSet<State>()

    val emptyStore = initialStore.toBottom()

    // Update the state's store. Queue the state again if it changed.
    fun mergeStateStore(state: State, store: MungoStore) {
      val currStore = stateToStore[state] ?: emptyStore
      // Invalidate public fields since anything might have happened to them
      val newStore = currStore.leastUpperBoundFields(store).invalidateNonPrivateFields()
      if (!stateToStore.containsKey(state) || currStore != newStore) {
        stateToStore[state] = newStore
        stateQueue.add(state)
      }
    }

    // Returns the merge result if it changed. Returns null otherwise.
    fun mergeMethodStore(method: MethodTree, store: MungoStore): MungoStore? {
      val currStore = methodToStore[method] ?: emptyStore
      val newStore = currStore.leastUpperBoundFields(store)
      return if (!methodToStore.containsKey(method) || currStore != newStore) {
        methodToStore[method] = newStore
        newStore
      } else null
    }

    mergeStateStore(graph.getInitialState(), initialStore)

    while (stateQueue.isNotEmpty()) {
      val state = stateQueue.first()
      stateQueue.remove(state)

      val store = stateToStore[state]!!
      val methodToStates = methodToStatesCache.computeIfAbsent(state, ::getMethodToState)

      for ((method, destState) in methodToStates) {
        val entryStore = mergeMethodStore(method, store) ?: continue
        val result = analyze(entryStore, method)

        val returnStores = a.returnStatementStores
        val constantReturn = getConstantReturn(returnStores.map { it.first })

        // Merge new exit store with the stores of each destination state
        when (destState) {
          is State -> mergeStateStore(destState, result.regularStore)
          is DecisionState -> {
            // TODO handle enumeration values as well
            for ((label, dest) in destState.transitions) {
              when (label.label) {
                "true" -> mergeStateStore(dest, if (constantReturn != false) result.thenStore else emptyStore)
                "false" -> mergeStateStore(dest, if (constantReturn != true) result.elseStore else emptyStore)
                else -> mergeStateStore(dest, result.regularStore)
              }
            }
          }
        }
      }
    }

    // Finally, combine results into flowResult...
    f.combineFlowResults(results.values)

    // And save the state -> store mapping for later checking
    f.storeClassResult(classTree, stateToStore)
  }

  private fun analyzeClassWithoutProtocol(
    classTree: JCTree.JCClassDecl,
    publicMethods: List<UnderlyingAST.CFGMethod>,
    initialStore: MungoStore
  ) {
    // Since this class has no protocol, all methods are available.
    // It is as if it had only one state, and methods lead always to that state.
    var globalStore = initialStore.invalidateNonPrivateFields()
    var reanalyze = true

    // Update the global store. Analyze again if changed.
    fun updateGlobalStore(store: MungoStore) {
      val currStore = globalStore
      // Invalidate public fields since anything might have happened to them
      val newStore = currStore.leastUpperBoundFields(store).invalidateNonPrivateFields()
      if (currStore != newStore) {
        globalStore = newStore
        reanalyze = true
      }
    }

    while (reanalyze) {
      reanalyze = false

      val entryStore = globalStore

      for (astMethod in publicMethods) {
        val result = analyze(entryStore, astMethod.method)
        // Merge new exit store with the global store
        updateGlobalStore(result.regularStore)
      }
    }

    // Finally, combine results into flowResult...
    f.combineFlowResults(results.values)

    // And save global store for later checking
    f.storeClassResult(classTree, globalStore)
  }

  private fun getConstantReturn(returnStores: List<ReturnNode>): Boolean? {
    var sawTrue = false
    var sawFalse = false
    for (ret in returnStores) {
      when (val result = ret.result) {
        is BooleanLiteralNode -> if (result.value!!) {
          if (sawFalse) return null
          sawTrue = true
        } else {
          if (sawTrue) return null
          sawFalse = true
        }
        else -> return null
      }
    }
    return sawTrue
  }

  private fun analyze(entryStore: MungoStore, method: MethodTree): TransferInput<MungoValue, MungoStore> {
    val cfg = methodToCFG[method] ?: error("no cfg")

    t.setFixedInitialStore(entryStore)
    a.performAnalysis(cfg, entryStore.getFields())

    val exitResult = a.getInput(cfg.regularExitBlock)!!
    val regularExitStore = exitResult.regularStore

    // Store/override result
    results[method] = a.result

    // Store/override exit and return statement stores
    val returnStores = a.returnStatementStores
    f.storeMethodResults(method, regularExitStore, returnStores)

    return exitResult
  }

}
