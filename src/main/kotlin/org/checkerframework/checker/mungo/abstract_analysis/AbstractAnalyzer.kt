package org.checkerframework.checker.mungo.abstract_analysis

import com.sun.source.tree.*
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.ClassInfo
import org.checkerframework.checker.mungo.analysis.StoreInfo
import org.checkerframework.checker.mungo.analysis.Worklist
import org.checkerframework.checker.mungo.analysis.prepareClass
import org.checkerframework.checker.mungo.typecheck.MungoType
import org.checkerframework.checker.mungo.typestate.graph.AbstractState
import org.checkerframework.checker.mungo.typestate.graph.DecisionState
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.checker.mungo.typestate.graph.State
import org.checkerframework.dataflow.analysis.Store.FlowRule
import org.checkerframework.dataflow.cfg.ControlFlowGraph
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.dataflow.cfg.UnderlyingAST.*
import org.checkerframework.dataflow.cfg.block.*
import org.checkerframework.dataflow.cfg.node.*
import org.checkerframework.framework.flow.CFCFGBuilder
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.javacutil.Pair
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import java.util.*
import javax.lang.model.type.TypeMirror
import org.checkerframework.dataflow.analysis.Store.Kind as StoreKind

abstract class AbstractAnalyzer<
  AnalyzerResult : AbstractAnalyzerResult<Store, MutableStore>,
  MutableAnalyzerResult : AbstractMutableAnalyzerResult<Store, MutableStore, AnalyzerResult>,
  MutableAnalyzerResultWithValue : AbstractMutableAnalyzerResultWithValue<StoreInfo, Store, MutableStore, AnalyzerResult>,
  StoreInfo : AbstractStoreInfo,
  Store : AbstractStore<Store, MutableStore>,
  MutableStore : AbstractMutableStore<Store, MutableStore>,
  StoreUtils : AbstractStoreUtils<Store, MutableStore>,
  StoreInfoUtils : AbstractStoreInfoUtils<StoreInfo>,
  AnalyzerResultsUtils : AbstractAnalyzerResultUtils<StoreInfo, Store, MutableStore, AnalyzerResult, MutableAnalyzerResult, MutableAnalyzerResultWithValue>
  >(
  checker: MungoChecker,
  val storeUtils: StoreUtils,
  val storeInfoUtils: StoreInfoUtils,
  val analyzerResultsUtils: AnalyzerResultsUtils
) : AbstractAnalyzerBase(checker) {

  lateinit var unknown: StoreInfo

  protected val worklist = Worklist()

  protected val treeLookup = IdentityHashMap<Tree, MutableSet<Node>>()

  protected val inputs = IdentityHashMap<Block, AnalyzerResult>()
  protected val resultsBefore = IdentityHashMap<Node, AnalyzerResult>()
  protected val resultsAfter = IdentityHashMap<Node, AnalyzerResult>()
  protected val resultsExit = IdentityHashMap<Tree, AnalyzerResult>()

  protected val nodeValues = IdentityHashMap<Node, StoreInfo>()
  protected val storesAtReturnStatements = IdentityHashMap<ReturnNode, AnalyzerResult>()
  protected var returnStatementStores = IdentityHashMap<Tree, List<Pair<ReturnNode, AnalyzerResult?>>>()

  abstract fun getInitialInfo(node: Node): StoreInfo

  fun getInferredInfoOptional(tree: Tree): StoreInfo? {
    val nodes = treeLookup[tree] ?: emptySet()
    var info: StoreInfo? = null
    for (node in nodes) {
      if (info == null) {
        info = nodeValues[node]
      } else {
        val other = nodeValues[node]
        if (other != null) {
          info = storeInfoUtils.merge(info, other)
        }
      }
    }
    return info
  }

  fun getInferredInfo(tree: Tree): StoreInfo {
    return getInferredInfoOptional(tree) ?: unknown
  }

  // Some inference results depend on nodeValues, which might have changed.
  // We track these dependencies so that we can rerun blocks even if the stores did not change.

  private lateinit var currentBlock: Block
  private val dependencies = WeakIdentityHashMap<Block, MutableSet<Pair<Node, StoreInfo?>>>()

  private fun addToWorklist(block: Block) {
    worklist.add(block)
    dependencies.remove(block)
  }

  private fun didNodeValuesChange(block: Block): Boolean {
    return dependencies[block]?.any { pair -> nodeValues[pair.first] != pair.second } ?: false
  }

  // Used during analysis
  fun getCurrentInferredInfo(node: Node, default: StoreInfo? = null): StoreInfo {
    val value = nodeValues[node] ?: default ?: getInitialInfo(node)
    dependencies.computeIfAbsent(currentBlock) { mutableSetOf() }.add(Pair.of(node, value))
    nodeValues[node] = value
    return value
  }

  fun getRegularExitStore(tree: Tree): Store? {
    return resultsExit[tree]?.getRegular()
  }

  fun getResultBefore(tree: Tree): AnalyzerResult {
    val nodes = treeLookup[tree] ?: emptySet()
    val result = analyzerResultsUtils.createMutableAnalyzerResult()
    for (node in nodes) {
      resultsBefore[node]?.let { result.merge(it) }
    }
    return analyzerResultsUtils.createAnalyzerResult(result)
  }

  fun getResultBefore(node: Node) = resultsBefore[node] ?: analyzerResultsUtils.createAnalyzerResult()

  fun getStoreBefore(tree: Tree) = getResultBefore(tree).getRegular()

  fun getStoreBefore(node: Node) = getResultBefore(node).getRegular()

  fun getResultExit(cfg: ControlFlowGraph): AnalyzerResult {
    val regularResult = inputs[cfg.regularExitBlock]
    // Might be null if a method ends with a thrown exception
    return regularResult ?: analyzerResultsUtils.createAnalyzerResult()
  }

  fun getResultExceptionalExit(cfg: ControlFlowGraph) = inputs[cfg.exceptionalExitBlock]

  fun getReturnStatementStores(cfg: ControlFlowGraph) = cfg.returnNodes.map {
    Pair.of(it, storesAtReturnStatements[it])
  }

  // Mapping from state to store for classes with protocol
  private val classTreeToStatesToStore = mutableMapOf<ClassTree, Map<State, Store>>()

  // Global upper bound store for classes without protocol
  private val classTreeToGlobalStore = mutableMapOf<ClassTree, Store>()

  fun getStatesToStore(tree: ClassTree) = classTreeToStatesToStore[tree]

  fun getGlobalStore(tree: ClassTree) = classTreeToGlobalStore[tree]

  private fun storeClassResult(classTree: ClassTree, stateToStore: Map<State, Store>) {
    classTreeToStatesToStore[classTree] = stateToStore
  }

  private fun storeClassResult(classTree: ClassTree, globalStore: Store) {
    classTreeToGlobalStore[classTree] = globalStore
  }

  // Null - No scanning
  // 1 - Scanning
  // 2 - Done
  private val scanning = mutableMapOf<ClassTree, Int>()

  fun run(classTree: ClassTree) {
    val classQueue: Queue<Pair<ClassTree, Store>> = ArrayDeque()
    classQueue.add(Pair.of(classTree, storeUtils.emptyStore()))

    while (!classQueue.isEmpty()) {
      val qel = classQueue.remove()
      val ct = qel.first

      if (scanning.containsKey(ct)) continue
      scanning[ct] = 1

      val graph = utils.classUtils.visitClassSymbol((ct as JCTree.JCClassDecl).sym)
      val info = prepareClass(ct)
      run(classQueue, ct, info.static, null)
      run(classQueue, ct, info.nonStatic, graph)

      scanning[ct] = 2
    }
  }

  abstract fun handleUninitializedField(store: MutableStore, field: VariableTree, ct: ClassTree)

  private fun run(classQueue: Queue<Pair<ClassTree, Store>>, classTree: JCTree.JCClassDecl, info: ClassInfo, graph: Graph?) {
    val lambdaQueue: Queue<Pair<LambdaExpressionTree, Store>> = ArrayDeque()

    // Static fields/initializers are executed when a class is first loaded in textual order
    // Instance fields/initializers are executed when an object is instantiated in textual order

    // TODO find out what the textual order is

    var currentStore = storeUtils.emptyStore()

    // Analyze fields
    for (field in info.fields) {
      val initializer = field.initializer
      if (initializer != null) {
        currentStore = run(
          classQueue,
          lambdaQueue,
          CFGStatement(field, classTree),
          currentStore
        ).getRegular()
      } else {
        val store = currentStore.toMutable()
        handleUninitializedField(store, field, classTree)
        currentStore = store.toImmutable()
      }
    }

    // Analyze blocks
    for (block in info.blocks) {
      currentStore = run(
        classQueue,
        lambdaQueue,
        CFGStatement(block, classTree),
        currentStore
      ).getRegular()
    }

    // The initial information for each constructor is the inferred information from the fields and blocks.
    // Since invocations of another constructors must be in the first line in a constructor, this is fine.
    // Ref: https://docs.oracle.com/javase/tutorial/java/javaOO/thiskey.html

    // To compute the initial information for public methods, merge the exit stores of all the constructors.
    // Even if a constructor calls another constructor, that should be fine
    // since we invalidate previous information upon calls.
    // In the worst case, all fields will be marked with the unknown type.

    val exitConstructorsStore = storeUtils.mutableEmptyStore()

    // Analyze constructors
    for (method in info.constructorMethods) {
      val result = run(
        classQueue,
        lambdaQueue,
        CFGMethod(method, classTree),
        currentStore
      )
      exitConstructorsStore.mergeFields(result.getRegular())
    }

    // The initial information for non public methods, is the worst case scenario: all the fields invalidated.
    // TODO improve this by using the upper bound of the stores of all public methods, instead of invalidating everything
    // TODO or performing more complex analysis
    val storeForNonPublicMethods = exitConstructorsStore.toMutable().invalidateFields(this).toImmutable()

    // Analyze non public methods
    for (method in info.nonPublicMethods) {
      run(
        classQueue,
        lambdaQueue,
        CFGMethod(method, classTree),
        storeForNonPublicMethods
      )
    }

    val storeForPublicMethods = exitConstructorsStore.toImmutable()

    // Analyze public methods
    if (graph == null) {
      analyzeClassWithoutProtocol(classQueue, lambdaQueue, classTree, info.publicMethods, storeForPublicMethods)
    } else {
      analyzeClassWithProtocol(classQueue, lambdaQueue, classTree, info.publicMethods, graph, storeForPublicMethods)
    }

    // Analyze lambdas
    while (!lambdaQueue.isEmpty()) {
      val lambdaPair = lambdaQueue.poll()
      val mt = TreeUtils.enclosingOfKind(utils.getPath(lambdaPair.first, root), Tree.Kind.METHOD) as MethodTree
      run(
        classQueue,
        lambdaQueue,
        CFGLambda(lambdaPair.first, classTree, mt),
        lambdaPair.second
      )
    }
  }

  private fun mergeTreeLookup(otherTreeLookup: IdentityHashMap<Tree, MutableSet<Node>>) {
    for ((key, value) in otherTreeLookup) {
      val hit = treeLookup[key]
      if (hit == null) {
        treeLookup[key] = value
      } else {
        hit.addAll(value)
      }
    }
  }

  private fun astToTree(ast: UnderlyingAST) = when (ast) {
    is CFGMethod -> ast.method
    is CFGLambda -> ast.code
    is CFGStatement -> ast.code
    else -> throw RuntimeException("unknown ast")
  }

  private val cfgCache = WeakIdentityHashMap<Tree, ControlFlowGraph>()

  abstract fun initialStore(capturedStore: Store, cfg: ControlFlowGraph): Store

  private fun run(
    classQueue: Queue<Pair<ClassTree, Store>>,
    lambdaQueue: Queue<Pair<LambdaExpressionTree, Store>>,
    ast: UnderlyingAST,
    capturedStore: Store
  ): AnalyzerResult {
    val tree = astToTree(ast)
    val inCache = cfgCache[tree]
    val cfg = if (inCache == null) {
      val g = CFCFGBuilder.build(root, ast, processingEnv)
      mergeTreeLookup(g.treeLookup)
      cfgCache[tree] = g
      g
    } else inCache

    // Init
    val entry = cfg.entryBlock
    worklist.process(cfg)
    worklist.add(entry)
    val store = initialStore(capturedStore, cfg)
    inputs[entry] = analyzerResultsUtils.createAnalyzerResult(store, store)

    // Run
    var block = worklist.poll()
    while (block != null) {
      run(block)
      block = worklist.poll()
    }

    // Store results
    val exitResult = getResultExit(cfg)
    resultsExit[tree] = exitResult
    returnStatementStores[tree] = getReturnStatementStores(cfg)

    // Graphics
    /*if (checker.hasOption("flowdotdir") || checker.hasOption("cfgviz")) {
      handleCFGViz()
    }*/

    // Only inner queue classes and lambdas once
    if (inCache == null) {
      // Queue classes
      for (cls in cfg.declaredClasses) {
        // TODO which store to use? getStoreBefore(cls)
        classQueue.add(Pair.of(cls, storeUtils.emptyStore()))
      }

      // Queue lambdas
      for (lambda in cfg.declaredLambdas) {
        // TODO which store to use? getStoreBefore(cls)
        lambdaQueue.add(Pair.of(lambda, storeUtils.emptyStore()))
      }
    }

    return exitResult
  }

  private fun run(block: Block) {
    currentBlock = block

    val inputBefore = inputs[block]!!
    when (block) {
      is RegularBlock -> {
        val succ = block.successor!!
        var result = inputBefore
        for (n in block.nodes) {
          result = callInferrer(n, result)
        }
        propagateStoresTo(succ, result, block.flowRule)
      }
      is ExceptionBlock -> {
        val node = block.node
        val succ = block.successor
        val result = callInferrer(node, inputBefore)

        // TODO handle possible exceptions

        // Propagate store
        if (succ != null) {
          propagateStoresTo(succ, result, block.flowRule)
        }

        // Propagate store to exceptional successors
        for ((cause, value) in block.exceptionalSuccessors) {
          val exceptionalStore = result.getExceptionalStore(cause)
          if (exceptionalStore != null) {
            for (exceptionSucc in value) {
              addStoreBefore(
                exceptionSucc,
                exceptionalStore,
                StoreKind.BOTH)
            }
          } else {
            for (exceptionSucc in value) {
              addStoreBefore(
                exceptionSucc,
                inputBefore.getRegular(),
                StoreKind.BOTH)
            }
          }
        }
      }
      is ConditionalBlock -> {
        propagateStoresTo(block.thenSuccessor, inputBefore, block.thenFlowRule)
        propagateStoresTo(block.elseSuccessor, inputBefore, block.elseFlowRule)
      }
      is SpecialBlock -> {
        // Special basic blocks are empty and cannot throw exceptions,
        // thus there is no need to perform any analysis.
        val succ = block.successor
        if (succ != null) {
          propagateStoresTo(succ, inputBefore, block.flowRule)
        }
      }
      else -> throw RuntimeException("Unexpected block type: " + block.type)
    }
  }

  abstract fun visit(node: Node, mutableResult: MutableAnalyzerResultWithValue)

  private fun callInferrer(node: Node, input: AnalyzerResult): AnalyzerResult {
    // Store previous result
    resultsBefore[node] = input

    if (node.isLValue) {
      resultsAfter[node] = input
      return input
    }

    val initialValue = getInitialInfo(node)
    val mutableResult = analyzerResultsUtils.createMutableAnalyzerResultWithValue(initialValue, input)

    visit(node, mutableResult)

    // Merge then and else stores
    if (!shouldEachToEach(node)) {
      mutableResult.mergeThenAndElse()
    }

    // Store node value
    nodeValues[node] = mutableResult.getValue()

    // Store after result
    val result = analyzerResultsUtils.createAnalyzerResult(mutableResult.getThen(), mutableResult.getElse())

    if (node is ReturnNode) {
      storesAtReturnStatements[node] = result
    }

    resultsAfter[node] = result
    return result
  }

  fun nextIsConditional(node: Node): Boolean {
    val block = node.block
    if (block is RegularBlock) {
      if (block.successor is ConditionalBlock) {
        return block.lastNode === node
      }
    }
    return false
  }

  private fun shouldEachToEach(node: Node): Boolean {
    return when (val block = node.block) {
      is RegularBlock -> {
        val idx = block.nodes.indexOf(node)
        val nextIdx = idx + 1
        if (nextIdx < block.nodes.size) {
          return shouldEachToEach(node, block.nodes[nextIdx])
        }
        return shouldEachToEach(node, block.successor)
      }
      is ExceptionBlock -> return shouldEachToEach(node, block.successor)
      else -> false
    }
  }

  private fun shouldEachToEach(node: Node?, succ: Block?): Boolean {
    return when (succ) {
      is ConditionalBlock -> true
      is SpecialBlock -> succ.specialType == SpecialBlock.SpecialBlockType.EXIT
      is RegularBlock -> shouldEachToEach(node, succ.nodes.firstOrNull())
      else -> false
    }
  }

  private fun shouldEachToEach(node: Node?, after: Node?): Boolean {
    return when (after) {
      is ReturnNode -> after.result === node
      is ConditionalNotNode -> after.operand === node
      else -> false
    }
  }

  private fun propagateStoresTo(
    succ: Block,
    currentInput: AnalyzerResult,
    flowRule: FlowRule
  ) {
    when (flowRule) {
      FlowRule.EACH_TO_EACH -> {
        addStoreBefore(
          succ,
          currentInput.getThen(),
          StoreKind.THEN)
        addStoreBefore(
          succ,
          currentInput.getElse(),
          StoreKind.ELSE)
      }
      FlowRule.THEN_TO_BOTH -> addStoreBefore(
        succ,
        currentInput.getThen(),
        StoreKind.BOTH)
      FlowRule.ELSE_TO_BOTH -> addStoreBefore(
        succ,
        currentInput.getElse(),
        StoreKind.BOTH)
      FlowRule.THEN_TO_THEN -> addStoreBefore(
        succ,
        currentInput.getThen(),
        StoreKind.THEN)
      FlowRule.ELSE_TO_ELSE -> addStoreBefore(
        succ,
        currentInput.getElse(),
        StoreKind.ELSE)
    }
  }

  private fun addStoreBefore(
    b: Block,
    s: Store,
    kind: StoreKind
  ) {
    val input = inputs[b]
    val thenStore = input?.getThen() ?: storeUtils.emptyStore()
    val elseStore = input?.getElse() ?: storeUtils.emptyStore()
    when (kind) {
      StoreKind.THEN -> {
        // Update the then store
        val newThenStore = storeUtils.merge(s, thenStore)
        if (input == null || newThenStore != thenStore) {
          inputs[b] = analyzerResultsUtils.createAnalyzerResult(newThenStore, elseStore)
          addToWorklist(b)
        } else if (didNodeValuesChange(b)) {
          addToWorklist(b)
        }
      }
      StoreKind.ELSE -> {
        // Update the else store
        val newElseStore = storeUtils.merge(s, elseStore)
        if (input == null || newElseStore != elseStore) {
          inputs[b] = analyzerResultsUtils.createAnalyzerResult(thenStore, newElseStore)
          addToWorklist(b)
        } else if (didNodeValuesChange(b)) {
          addToWorklist(b)
        }
      }
      StoreKind.BOTH -> {
        val sameStore = thenStore === elseStore
        if (sameStore) {
          // Currently there is only one regular store
          val newStore = storeUtils.merge(s, thenStore)
          if (input == null || newStore != thenStore) {
            inputs[b] = analyzerResultsUtils.createAnalyzerResult(newStore, newStore)
            addToWorklist(b)
          } else if (didNodeValuesChange(b)) {
            addToWorklist(b)
          }
        } else {
          val newThenStore = storeUtils.merge(s, thenStore)
          val newElseStore = storeUtils.merge(s, elseStore)
          if (input == null || newThenStore != thenStore || newElseStore != elseStore) {
            inputs[b] = analyzerResultsUtils.createAnalyzerResult(newThenStore, newElseStore)
            addToWorklist(b)
          } else if (didNodeValuesChange(b)) {
            addToWorklist(b)
          }
        }
      }
    }
  }

  // Class analysis

  private fun analyzeClassWithProtocol(
    classQueue: Queue<Pair<ClassTree, Store>>,
    lambdaQueue: Queue<Pair<LambdaExpressionTree, Store>>,
    classTree: JCTree.JCClassDecl,
    publicMethods: List<MethodTree>,
    graph: Graph,
    initialStore: Store
  ) {
    val methodsWithTypes = publicMethods.map {
      Pair(it, TreeUtils.elementFromTree(it) as Symbol.MethodSymbol)
    }

    val methodToStatesCache = mutableMapOf<State, Map<MethodTree, AbstractState<*>>>()
    val env = graph.getEnv()

    fun getMethodToState(state: State) = run {
      methodsWithTypes.mapNotNull { (method, symbol) ->
        val t = state.transitions.entries.find { utils.methodUtils.sameMethod(env, symbol, it.key) }
        t?.value?.let { Pair(method, it) }
      }.toMap()
    }

    // States lead us to methods that may be called. So we need information about each state.
    val stateToStore = mutableMapOf<State, Store>()
    // But since the same method may be available from different states,
    // we also need to store the entry store for each method.
    val methodToStore = mutableMapOf<MethodTree, Store>()
    // States that need recomputing. Use a LinkedHashSet to keep some order and avoid duplicates.
    val stateQueue = LinkedHashSet<State>()

    val emptyStore = initialStore.toMutable().toBottom().toImmutable()

    // Update the state's store. Queue the state again if it changed.
    fun mergeStateStore(state: State, store: Store) {
      val currStore = stateToStore[state] ?: emptyStore
      // Invalidate public fields since anything might have happened to them
      val newStore = storeUtils.mutableMergeFields(currStore, store).invalidatePublicFields(this).toImmutable()
      if (!stateToStore.containsKey(state) || currStore != newStore) {
        stateToStore[state] = newStore
        stateQueue.add(state)
      }
    }

    // Returns the merge result if it changed. Returns null otherwise.
    fun mergeMethodStore(method: MethodTree, store: Store): Store? {
      val currStore = methodToStore[method] ?: emptyStore
      val newStore = storeUtils.mutableMergeFields(currStore, store).toImmutable()
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
        val result = run(classQueue, lambdaQueue, CFGMethod(method, classTree), entryStore)
        val constantReturn = getConstantReturn(returnStatementStores[method]!!.map { it.first })

        // Merge new exit store with the stores of each destination state
        when (destState) {
          is State -> mergeStateStore(destState, result.getRegular())
          is DecisionState -> {
            // TODO handle enumeration values as well
            for ((label, dest) in destState.transitions) {
              when (label.label) {
                "true" -> mergeStateStore(dest, if (constantReturn != false) result.getThen() else emptyStore)
                "false" -> mergeStateStore(dest, if (constantReturn != true) result.getElse() else emptyStore)
                else -> mergeStateStore(dest, result.getRegular())
              }
            }
          }
        }
      }
    }

    // And save the state -> store mapping for later checking
    storeClassResult(classTree, stateToStore)
  }

  private fun analyzeClassWithoutProtocol(
    classQueue: Queue<Pair<ClassTree, Store>>,
    lambdaQueue: Queue<Pair<LambdaExpressionTree, Store>>,
    classTree: JCTree.JCClassDecl,
    publicMethods: List<MethodTree>,
    initialStore: Store
  ) {
    // Since this class has no protocol, all methods are available.
    // It is as if it had only one state, and methods lead always to that state.
    var globalStore = initialStore.toMutable().invalidatePublicFields(this).toImmutable()
    var reanalyze = true

    // Update the global store. Analyze again if changed.
    fun updateGlobalStore(store: Store) {
      val currStore = globalStore
      // Invalidate public fields since anything might have happened to them
      val newStore = storeUtils.mutableMergeFields(currStore, store).invalidatePublicFields(this).toImmutable()
      if (currStore != newStore) {
        globalStore = newStore
        reanalyze = true
      }
    }

    while (reanalyze) {
      reanalyze = false

      val entryStore = globalStore

      for (method in publicMethods) {
        val result = run(classQueue, lambdaQueue, CFGMethod(method, classTree), entryStore)
        // Merge new exit store with the global store
        updateGlobalStore(result.getRegular())
      }
    }

    // And save global store for later checking
    storeClassResult(classTree, globalStore)
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

}
