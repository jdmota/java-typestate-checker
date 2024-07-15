package jatyc.core.cfg

import jatyc.core.linearmode.Store
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import java.util.*

abstract class CfgVisitor<A : Store> {

  abstract fun analyzeNode(func: FuncDeclaration, pre: A, node: SimpleNode, post: A)
  abstract fun defaultAssertion(node: SimpleNode): A
  abstract fun cleanUp(code: CodeExpr)
  abstract fun makeInitialAssertion(func: FuncDeclaration, cfg: SimpleCFG, initialAssertion: A): A
  abstract fun propagate(edge: SimpleEdge, a: A, b: A, override: Boolean): Boolean // True if it should analyze again
  abstract fun analyzeEnd(func: FuncDeclaration, exitAssertion: A)

  private val assertions = IdentityHashMap<SimpleNode, Pair<A, A>>()
  private val debug = { func: FuncDeclaration -> false }
  private val debugAll = false
  private val debugAllMore = false

  private val LOOP_LIMIT = 30

  private var inOverrideMode = false
  protected fun getOverrideMode() = inOverrideMode

  fun analyze(func: FuncDeclaration, initialAssertion: A): A {
    return try {
      inOverrideMode = true
      analyzeFunc(func, initialAssertion)
    } catch (error: LoopLimitException) {
      inOverrideMode = false
      analyzeFunc(func, initialAssertion)
    }
  }

  private fun analyzeFunc(func: FuncDeclaration, initialAssertion: A): A {
    val seen = WeakIdentityHashMap<SimpleNode, Int>()
    val cfg = func.body

    // Clean up
    for (node in cfg.allNodes) {
      assertions.remove(node)
      if (node is SimpleCodeNode) {
        cleanUp(node.code)
      }
    }

    // Prepare
    val worklist = Worklist()
    worklist.process(cfg)
    worklist.add(cfg.entry)

    val assertion = makeInitialAssertion(func, cfg, initialAssertion)
    assertions[cfg.entry] = Pair(assertion, assertion)

    if (debug(func)) {
      println("$func : pre assertion = $assertion")
    }

    var node = worklist.poll()
    while (node != null) {
      if (inOverrideMode) {
        val times = seen.computeIfAbsent(node) { 0 }
        seen[node] = times + 1
        if (times >= LOOP_LIMIT) {
          throw LoopLimitException()
        }
      }

      analyze(worklist, func, node)
      node = worklist.poll()
    }

    val endAssertion = getAssertions(cfg.exit).second
    analyzeEnd(func, endAssertion)

    if (debug(func)) {
      println("$func : post assertion = $endAssertion\n")
    }
    return endAssertion
  }

  fun getAssertions(node: SimpleNode): Pair<A, A> {
    // (pre, post)
    return assertions.computeIfAbsent(node) { Pair(defaultAssertion(it), defaultAssertion(it)) }
  }

  private fun analyze(worklist: Worklist, func: FuncDeclaration, node: SimpleNode) {
    val (pre, post) = getAssertions(node)
    analyzeNode(func, pre, node, post)

    if (debugAll && debug(func)) {
      println("analyzing: ${node.javaClass} : ${if (node is SimpleCodeNode) node.code.toString() else ""}")
      println("pre : $pre")
      println("post : $post\n")
    }

    for (edge in node.outEdges) {
      val child = edge.to
      if (debugAllMore && debug(func)) {
        println("child : ${child.javaClass} : $child")
      }
      val firstTime = !assertions.containsKey(child)
      val (childPre, _) = getAssertions(child)
      if (propagateJob(edge, post, childPre) || firstTime) {
        worklist.add(child)
        if (debugAllMore && debug(func)) {
          println("propagated! changed!")
          println("parent post $post ; child pre $childPre")
        }
      } else {
        if (debugAllMore && debug(func)) {
          println("propagated! did not change!")
        }
      }
    }
  }

  private fun propagateJob(edge: SimpleEdge, a: A, b: A): Boolean {
    return if (inOverrideMode) {
      val store = defaultAssertion(edge.to)
      if (edge.backEdge) {
        edge.to.inEdgesBack().forEach { propagate(it, getAssertions(it.from).second, store, false) }
      } else {
        edge.to.inEdgesNotBack().forEach { propagate(it, getAssertions(it.from).second, store, false) }
      }
      if (store.hasBottom()) {
        return store.toBottom().propagateTo(b)
      }
      store.overrideTo(b)
    } else {
      propagate(edge, a, b, false)
    }
  }

}

class LoopLimitException : Throwable() {

}
