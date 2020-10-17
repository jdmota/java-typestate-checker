package org.checkerframework.checker.mungo.assertions

import com.sun.source.tree.*
import com.sun.tools.javac.code.TypeTag
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.*
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
  private val assertions = WeakIdentityHashMap<Node, NodeAssertions>()
  private val specialAssertions = WeakIdentityHashMap<SpecialBlock, NodeAssertions>()
  private val constraints = Constraints()

  fun debug() {
    for ((node, assertions) in assertions) {
      if (assertions.preThen !== assertions.preElse) {
        println("then: ${assertions.preThen}; else: ${assertions.preElse}")
      } else {
        println(assertions.preThen)
      }
      println(node)
      if (assertions.postThen !== assertions.postElse) {
        println("then: ${assertions.postThen}; else: ${assertions.postElse}")
      } else {
        println(assertions.postThen)
      }
    }
    println("----")
    constraints.debug()
  }

  fun run(classTree: ClassTree) {
    val classQueue: Queue<Pair<ClassTree, Set<Reference>>> = ArrayDeque()
    classQueue.add(Pair.of(classTree, emptySet()))

    while (!classQueue.isEmpty()) {
      val qel = classQueue.remove()
      val ct = qel.first as JCTree.JCClassDecl
      val outerLocations = qel.second

      val info = prepareClass(ct)
      run(classQueue, ct, info.static, outerLocations)
      run(classQueue, ct, info.nonStatic, outerLocations)
    }
  }

  private fun run(
    classQueue: Queue<Pair<ClassTree, Set<Reference>>>,
    classTree: JCTree.JCClassDecl,
    info: ClassInfo,
    outerLocations: Set<Reference>
  ) {
    val lambdaQueue: Queue<Pair<LambdaExpressionTree, Set<Reference>>> = ArrayDeque()

    // Analyze fields
    for (field in info.fields) {
      if ((field as JCTree.JCVariableDecl).initializer == null) {
        val nullTree = utils.maker.Literal(TypeTag.BOT, null)
        nullTree.pos = field.pos
        field.init = nullTree
      }
      run(
        classQueue,
        lambdaQueue,
        UnderlyingAST.CFGStatement(field, classTree),
        outerLocations
      )
    }

    // Analyze blocks
    for (block in info.blocks) {
      run(
        classQueue,
        lambdaQueue,
        UnderlyingAST.CFGStatement(block, classTree),
        outerLocations
      )
    }

    // Analyze methods
    for (method in info.methods) {
      run(
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
      run(
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

  private fun run(
    classQueue: Queue<Pair<ClassTree, Set<Reference>>>,
    lambdaQueue: Queue<Pair<LambdaExpressionTree, Set<Reference>>>,
    ast: UnderlyingAST,
    otherLocations: Set<Reference>
  ) {
    val tree = astToTree(ast)
    val cfg = CFCFGBuilder.build(root, ast, processingEnv)
    cfgCache[tree] = cfg

    val locations = phase1(cfg).plus(otherLocations)
    phase2(cfg)

    // Queue classes
    for (cls in cfg.declaredClasses) {
      classQueue.add(Pair.of(cls, locations))
    }

    // Queue lambdas
    for (lambda in cfg.declaredLambdas) {
      lambdaQueue.add(Pair.of(lambda, locations))
    }
  }

  fun phase1(cfg: ControlFlowGraph): Set<Reference> {
    val ast = cfg.underlyingAST
    val locations = locationsGatherer.getParameterLocations(ast).toMutableSet()
    for (node in cfg.allNodes) {
      getReference(node)?.let { locations.addAll(locationsGatherer.getLocations(it)) }
    }
    // Lambdas with only one expression, do not have explicit return nodes
    if (ast is UnderlyingAST.CFGLambda) {
      val lambda = ast.lambdaTree
      if (lambda.bodyKind == LambdaExpressionTree.BodyKind.EXPRESSION) {
        locations.add(ReturnSpecialVar(treeToType(lambda.body)))
      }
    }
    return locations
  }

  fun phase2(cfg: ControlFlowGraph) {
    // Entry
    val pre = SymbolicAssertion()
    val entry = NodeAssertions(pre, pre, pre, pre)
    specialAssertions[cfg.entryBlock] = entry

    // Exits
    val preThen = SymbolicAssertion()
    val preElse = SymbolicAssertion()
    specialAssertions[cfg.regularExitBlock] = NodeAssertions(preThen, preElse, preThen, preElse)

    // Traverse
    traverse(entry, cfg.entryBlock, cfg.entryBlock.flowRule)
  }

  private fun traverse(prev: NodeAssertions, block: Block, flowRule: Store.FlowRule) {
    when (block) {
      is RegularBlock -> {
        var last = prev
        var lastFlow = flowRule
        for (n in block.nodes) {
          if (!traverse(last, n, lastFlow)) {
            return
          }
          last = assertions[n]!!
          lastFlow = Store.FlowRule.EACH_TO_EACH
        }
        block.successor?.let { traverse(last, it, block.flowRule) }
      }
      is ExceptionBlock -> {
        if (!traverse(prev, block.node, flowRule)) {
          return
        }
        block.successor?.let { traverse(assertions[block.node]!!, it, block.flowRule) }
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

  private fun traverse(prev: NodeAssertions, node: Node, flowRule: Store.FlowRule): Boolean {
    var keepGoing = false
    val nodeAssertions: NodeAssertions

    if (!assertions.containsKey(node)) {
      val preThen: SymbolicAssertion
      val preElse: SymbolicAssertion
      val postThen: SymbolicAssertion
      val postElse: SymbolicAssertion

      if (prev.postThen !== prev.postElse) {
        preThen = SymbolicAssertion()
        preElse = SymbolicAssertion()
      } else {
        preThen = SymbolicAssertion()
        preElse = preThen
      }

      if (shouldEachToEach(node)) {
        postThen = SymbolicAssertion()
        postElse = SymbolicAssertion()
      } else {
        postThen = SymbolicAssertion()
        postElse = postThen
      }

      nodeAssertions = NodeAssertions(preThen, preElse, postThen, postElse)
      assertions[node] = nodeAssertions

      keepGoing = true
    } else {
      nodeAssertions = assertions[node]!!
    }

    implies(prev, nodeAssertions, flowRule)
    return keepGoing
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

}
