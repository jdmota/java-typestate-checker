package org.checkerframework.checker.jtc.core.cfg

import org.checkerframework.checker.jtc.core.linearmode.Store
import java.util.*

abstract class CfgVisitor<A: Store> {

  abstract fun analyzeNode(func: FuncDeclaration, pre: A, node: SimpleNode, post: A)
  abstract fun defaultAssertion(node: SimpleNode): A
  abstract fun makeInitialAssertion(func: FuncDeclaration, cfg: SimpleCFG, initialAssertion: A): A
  abstract fun propagate(from: SimpleNode, rule: SimpleFlowRule, a: A, b: A): Boolean // True if it should analyze again
  abstract fun analyzeEnd(func: FuncDeclaration, exitAssertion: A)

  private val assertions = IdentityHashMap<SimpleNode, Pair<A, A>>()
  private var debug = false

  fun analyze(func: FuncDeclaration, initialAssertion: A): A {
    val cfg = func.body

    // Clean up
    for (node in cfg.allNodes) {
      assertions.remove(node)
    }

    // Prepare
    val worklist = Worklist()
    worklist.process(cfg)
    worklist.add(cfg.entry)

    val assertion = makeInitialAssertion(func, cfg, initialAssertion)
    assertions[cfg.entry] = Pair(assertion, assertion)

    if (debug) {
      println(assertion)
    }

    var node = worklist.poll()
    while (node != null) {
      analyze(worklist, func, node)
      node = worklist.poll()
    }

    val endAssertion = getAssertions(cfg.exit).second
    analyzeEnd(func, endAssertion)
    return endAssertion
  }

  fun getAssertions(node: SimpleNode): Pair<A, A> {
    // (pre, post)
    return assertions.computeIfAbsent(node) { Pair(defaultAssertion(it), defaultAssertion(it)) }
  }

  private fun analyze(worklist: Worklist, func: FuncDeclaration, node: SimpleNode) {
    val (pre, post) = getAssertions(node)
    analyzeNode(func, pre, node, post)

    if (debug) {
      println("analyzing: ${node.javaClass} : ${if (node is SimpleCodeNode) node.code.toString() else ""}")
      println("pre : $pre")
      println("post : $post")
    }

    for ((rule, child) in node.outEdges) {
      if (debug) {
        println("child : ${child.javaClass} : $child")
      }
      val firstTime = !assertions.containsKey(child)
      val (childPre, _) = getAssertions(child)
      if (propagate(node, rule, post, childPre) || firstTime) {
        worklist.add(child)
        if (debug) {
          println("propagated! changed!")
          println("parent post $post ; child pre $childPre")
        }
      } else {
        if (debug) {
          println("propagated! did node change!")
        }
      }
    }
  }

}
