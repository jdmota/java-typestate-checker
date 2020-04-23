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
import org.checkerframework.dataflow.cfg.ControlFlowGraph
import org.checkerframework.dataflow.cfg.UnderlyingAST
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

  fun analyzeClass(
    classQueue: Queue<org.checkerframework.javacutil.Pair<ClassTree, MungoStore?>>,
    lambdaQueue: Queue<org.checkerframework.javacutil.Pair<LambdaExpressionTree, MungoStore?>>,
    root: CompilationUnitTree?,
    classTree: JCTree.JCClassDecl,
    publicMethods: List<UnderlyingAST.CFGMethod>,
    graph: Graph,
    initialStore: MungoStore
  ) {
    val methodToCFG = mutableMapOf<MethodTree, ControlFlowGraph>()

    // Pre-work
    for (method in publicMethods) {
      val cfg = CFCFGBuilder.build(root, method, c, f, c.processingEnvironment)
      methodToCFG[method.method] = cfg
      // TODO if (checker.hasOption("flowdotdir") || checker.hasOption("cfgviz")) handleCFGViz()
      // Add classes and lambdas declared in method
      for (cls in cfg.declaredClasses) classQueue.add(org.checkerframework.javacutil.Pair.of(cls, f.getStoreBefore(cls)))
      for (lambda in cfg.declaredLambdas) lambdaQueue.add(org.checkerframework.javacutil.Pair.of(lambda, f.getStoreBefore(lambda)))
    }

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
    // The results for each method to be merged later.
    val results = mutableMapOf<MethodTree, AnalysisResult<MungoValue, MungoStore>>()

    // Update the state's store. Queue the state again if it changed.
    fun mergeStateStore(state: State, store: MungoStore) {
      val currStore = stateToStore[state] ?: f.emptyStore
      val newStore = currStore.leastUpperBoundFields(store)
      if (currStore != newStore) {
        stateToStore[state] = newStore
        stateQueue.add(state)
      }
    }

    // Returns the merge result if it changed. Returns null otherwise.
    fun mergeMethodStore(method: MethodTree, store: MungoStore): MungoStore? {
      val currStore = methodToStore[method] ?: f.emptyStore
      val newStore = currStore.leastUpperBoundFields(store)
      return if (currStore != newStore) {
        methodToStore[method] = newStore
        newStore
      } else null
    }

    mergeStateStore(graph.getInitialState(), initialStore)

    a.inClassAnalysis = true

    while (stateQueue.isNotEmpty()) {
      val state = stateQueue.first()
      stateQueue.remove(state)

      val store = stateToStore[state]!!
      val methodToStates = methodToStatesCache.computeIfAbsent(state, ::getMethodToState)

      for ((method, destState) in methodToStates) {
        val entryStore = mergeMethodStore(method, store) ?: continue
        val cfg = methodToCFG[method]!!

        t.setFixedInitialStore(entryStore)
        a.performAnalysis(cfg, entryStore.getFields())

        val exitResult = a.getInput(cfg.regularExitBlock)!!
        val regularExitStore = exitResult.regularStore

        // Store/override result
        results[method] = a.result

        // Store/override exit and return statement stores
        f.storeMethodResults(method, regularExitStore)

        // Merge new exit store with the stores of each destination state
        when (destState) {
          is State -> mergeStateStore(destState, regularExitStore)
          is DecisionState -> {
            // TODO handle enumeration values as well
            for ((label, dest) in destState.transitions) {
              when (label.label) {
                "true" -> mergeStateStore(dest, exitResult.thenStore)
                "false" -> mergeStateStore(dest, exitResult.elseStore)
                else -> mergeStateStore(dest, regularExitStore)
              }
            }
          }
        }
      }
    }

    a.inClassAnalysis = false

    // Finally, combine results into flowResult...
    f.combineFlowResults(results.values)

    // And save the state -> store mapping for later checking
    f.storeClassResult(classTree, stateToStore)
  }

}
