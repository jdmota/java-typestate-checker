package org.checkerframework.checker.mungo.assertions

import com.sun.source.tree.CompilationUnitTree
import com.sun.source.tree.LambdaExpressionTree
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.Reference
import org.checkerframework.checker.mungo.analysis.ReturnSpecialVar
import org.checkerframework.checker.mungo.analysis.getReference
import org.checkerframework.checker.mungo.utils.treeToType
import org.checkerframework.dataflow.analysis.Store
import org.checkerframework.dataflow.cfg.ControlFlowGraph
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.dataflow.cfg.block.*
import org.checkerframework.dataflow.cfg.node.ConditionalNotNode
import org.checkerframework.dataflow.cfg.node.Node
import org.checkerframework.dataflow.cfg.node.ReturnNode
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap

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
