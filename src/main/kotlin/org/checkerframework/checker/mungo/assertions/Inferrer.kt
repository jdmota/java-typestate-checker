package org.checkerframework.checker.mungo.assertions

import com.sun.source.tree.*
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.checker.mungo.typecheck.*
import org.checkerframework.checker.mungo.utils.treeToType
import org.checkerframework.dataflow.analysis.Store
import org.checkerframework.dataflow.cfg.ControlFlowGraph
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.dataflow.cfg.block.*
import org.checkerframework.dataflow.cfg.node.ConditionalNotNode
import org.checkerframework.dataflow.cfg.node.Node
import org.checkerframework.dataflow.cfg.node.ReturnNode
import org.checkerframework.framework.flow.CFCFGBuilder
import org.checkerframework.javacutil.Pair
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import java.util.*

class Inferrer(val checker: MungoChecker) {

  val utils get() = checker.utils
  val processingEnv = checker.processingEnvironment

  lateinit var root: JCTree.JCCompilationUnit

  fun setRoot(root: CompilationUnitTree) {
    this.root = root as JCTree.JCCompilationUnit
  }

  private val locationsGatherer = LocationsGatherer(checker)
  private val assertions = IdentityHashMap<Node, NodeAssertions>()
  private val specialAssertions = IdentityHashMap<SpecialBlock, NodeAssertions>()
  private val constraints = Constraints()

  fun phase1(classTree: ClassTree) {
    val classQueue: Queue<Pair<ClassTree, Set<Reference>>> = ArrayDeque()
    classQueue.add(Pair.of(classTree, emptySet()))

    while (!classQueue.isEmpty()) {
      val qel = classQueue.remove()
      val ct = qel.first as JCTree.JCClassDecl
      val outerLocations = qel.second

      utils.classUtils.visitClassSymbol(ct.sym)?.let { graph ->
        graph.getAllConcreteStates().forEach {
          constraints.addType(MungoStateType.create(graph, it))
        }
      }

      val info = prepareClass(ct)
      phase1(classQueue, ct, info.static, outerLocations)
      phase1(classQueue, ct, info.nonStatic, outerLocations)
    }
  }

  private fun phase1(
    classQueue: Queue<Pair<ClassTree, Set<Reference>>>,
    classTree: JCTree.JCClassDecl,
    info: ClassInfo,
    outerLocations: Set<Reference>
  ) {
    val lambdaQueue: Queue<Pair<LambdaExpressionTree, Set<Reference>>> = ArrayDeque()

    // Analyze fields
    for (field in info.fields) {
      /*if ((field as JCTree.JCVariableDecl).initializer == null) {
        val nullTree = utils.maker.Literal(TypeTag.BOT, null)
        nullTree.pos = field.pos
        field.init = nullTree
      }*/
      if (field.initializer != null) {
        phase1(
          classQueue,
          lambdaQueue,
          UnderlyingAST.CFGStatement(field, classTree),
          outerLocations
        )
      }
    }

    // Analyze blocks
    for (block in info.blocks) {
      phase1(
        classQueue,
        lambdaQueue,
        UnderlyingAST.CFGStatement(block, classTree),
        outerLocations
      )
    }

    // Analyze methods
    for (method in info.methods) {
      phase1(
        classQueue,
        lambdaQueue,
        UnderlyingAST.CFGMethod(method, classTree),
        outerLocations
      )
    }

    // Analyze lambdas
    while (!lambdaQueue.isEmpty()) {
      val lambdaPair = lambdaQueue.poll()
      val mt = TreeUtils.enclosingOfKind(utils.getPath(lambdaPair.first, root), Tree.Kind.METHOD) as MethodTree
      phase1(
        classQueue,
        lambdaQueue,
        UnderlyingAST.CFGLambda(lambdaPair.first, classTree, mt),
        lambdaPair.second
      )
    }
  }

  private fun astToTree(ast: UnderlyingAST) = when (ast) {
    is UnderlyingAST.CFGMethod -> ast.method
    is UnderlyingAST.CFGLambda -> ast.code
    is UnderlyingAST.CFGStatement -> ast.code
    else -> throw RuntimeException("unknown ast")
  }

  private val cfgCache = WeakIdentityHashMap<Tree, ControlFlowGraph>()
  private var currentLocations = emptySet<Reference>()

  private fun phase1(
    classQueue: Queue<Pair<ClassTree, Set<Reference>>>,
    lambdaQueue: Queue<Pair<LambdaExpressionTree, Set<Reference>>>,
    ast: UnderlyingAST,
    outerLocations: Set<Reference>
  ) {
    // Generate the CFG
    val tree = astToTree(ast)
    val cfg = CFCFGBuilder.build(root, ast, processingEnv)
    cfgCache[tree] = cfg

    // Gather locations
    val locations = gatherLocations(cfg).plus(outerLocations)
    currentLocations = locations

    // Associate assertions before and after each node, and connect implications
    phase1(cfg)

    // Queue classes
    for (cls in cfg.declaredClasses) {
      classQueue.add(Pair.of(cls, locations))
    }

    // Queue lambdas
    for (lambda in cfg.declaredLambdas) {
      lambdaQueue.add(Pair.of(lambda, locations))
    }

    // Debug
    /*for (node in cfg.allNodes) {
      assertions[node]!!.debug(node.toString())
    }*/
  }

  private fun gatherLocations(cfg: ControlFlowGraph): Set<Reference> {
    val ast = cfg.underlyingAST
    val locations = locationsGatherer.getParameterLocations(ast).toMutableSet()
    for (node in cfg.allNodes) {
      getReference(node)?.let { locations.addAll(locationsGatherer.getLocations(it)) }
    }
    // Lambdas with only one expression, do not have explicit return nodes
    // So add a location representing the return value
    if (ast is UnderlyingAST.CFGLambda) {
      val lambda = ast.lambdaTree
      if (lambda.bodyKind == LambdaExpressionTree.BodyKind.EXPRESSION) {
        locations.add(ReturnSpecialVar(treeToType(lambda.body)))
      }
    }
    return locations
  }

  private fun phase1(cfg: ControlFlowGraph) {
    // Entry
    val preAndPost = SymbolicAssertion(currentLocations)
    val entry = NodeAssertions(preAndPost, preAndPost, preAndPost, preAndPost)
    specialAssertions[cfg.entryBlock] = entry

    // Exits
    val preThen = SymbolicAssertion(currentLocations)
    val preElse = SymbolicAssertion(currentLocations)
    specialAssertions[cfg.regularExitBlock] = NodeAssertions(preThen, preElse, preThen, preElse)

    // Traverse
    traverse(entry, cfg.entryBlock, Store.FlowRule.EACH_TO_EACH)
  }

  private fun traverse(prev: NodeAssertions, block: Block, flowRule: Store.FlowRule) {
    when (block) {
      is RegularBlock -> {
        var last = prev
        var lastFlow = flowRule
        for (n in block.nodes) {
          last = traverse(last, n, lastFlow) ?: return
          lastFlow = Store.FlowRule.EACH_TO_EACH
        }
        block.successor?.let { traverse(last, it, block.flowRule) }
      }
      is ExceptionBlock -> {
        val last = traverse(prev, block.node, flowRule) ?: return
        block.successor?.let { traverse(last, it, block.flowRule) }
        // TODO handle possible exceptions
      }
      is ConditionalBlock -> {
        block.thenSuccessor?.let { traverse(prev, it, block.thenFlowRule) }
        block.elseSuccessor?.let { traverse(prev, it, block.elseFlowRule) }
      }
      is SpecialBlock -> {
        block.successor?.let { traverse(prev, it, block.flowRule) }
        when (block.specialType!!) {
          SpecialBlock.SpecialBlockType.ENTRY -> {
          }
          SpecialBlock.SpecialBlockType.EXIT -> {
            implies(prev, specialAssertions[block]!!, flowRule)
          }
          SpecialBlock.SpecialBlockType.EXCEPTIONAL_EXIT -> {
            // TODO
          }
        }
      }
      else -> throw RuntimeException("Unexpected block type: " + block.type)
    }
  }

  private fun traverse(prev: NodeAssertions, node: Node, flowRule: Store.FlowRule): NodeAssertions? {
    return if (!assertions.containsKey(node)) {
      val preThen: SymbolicAssertion
      val preElse: SymbolicAssertion
      if (prev.postThen !== prev.postElse) {
        preThen = SymbolicAssertion(currentLocations)
        preElse = SymbolicAssertion(currentLocations)
      } else {
        preThen = SymbolicAssertion(currentLocations)
        preElse = preThen
      }

      val postThen: SymbolicAssertion
      val postElse: SymbolicAssertion
      if (shouldEachToEach(node)) {
        postThen = SymbolicAssertion(currentLocations)
        postElse = SymbolicAssertion(currentLocations)
      } else {
        postThen = SymbolicAssertion(currentLocations)
        postElse = postThen
      }

      val nodeAssertions = NodeAssertions(preThen, preElse, postThen, postElse)
      assertions[node] = nodeAssertions

      implies(prev, nodeAssertions, flowRule)
      nodeAssertions
    } else {
      implies(prev, assertions[node]!!, flowRule)
      null
    }
  }

  private fun implies(prev: NodeAssertions, next: NodeAssertions, flowRule: Store.FlowRule) {
    when (flowRule) {
      Store.FlowRule.EACH_TO_EACH -> {
        constraints.implies(prev.postThen, next.preThen)
        constraints.implies(prev.postElse, next.preElse)
      }
      Store.FlowRule.THEN_TO_BOTH -> {
        constraints.implies(prev.postThen, next.preThen)
        constraints.implies(prev.postThen, next.preElse)
      }
      Store.FlowRule.ELSE_TO_BOTH -> {
        constraints.implies(prev.postElse, next.preThen)
        constraints.implies(prev.postElse, next.preElse)
      }
      Store.FlowRule.THEN_TO_THEN -> {
        constraints.implies(prev.postThen, next.preThen)
      }
      Store.FlowRule.ELSE_TO_ELSE -> {
        constraints.implies(prev.postElse, next.preElse)
      }
    }
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

  fun phase2() {
    println("Starting phase 2...")

    constraints.start()

    println("Inferring constraints...")

    val visitor = ConstraintsInference(this, constraints)
    for ((node, assertions) in assertions) {
      node.accept(visitor, assertions)
    }

    val solution = constraints.end()

    if (solution == null) {
      println("Error!\n")
    } else {
      println("Correct!\n")

      for ((node, assertions) in assertions) {
        assertions.debug(solution, node.toString())
      }
    }
  }

}
