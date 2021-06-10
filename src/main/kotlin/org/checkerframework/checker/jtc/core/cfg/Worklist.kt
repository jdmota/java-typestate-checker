package org.checkerframework.checker.jtc.core.cfg

import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import java.util.*

// Adapted from org.checkerframework.dataflow.analysis.Analysis.Worklist

class Worklist {
  private val depthFirstOrder: IdentityHashMap<SimpleNode, Int> = IdentityHashMap()

  inner class DFOComparator : Comparator<SimpleNode> {
    override fun compare(b1: SimpleNode, b2: SimpleNode): Int {
      return depthFirstOrder[b1]!! - depthFirstOrder[b2]!!
    }
  }

  private val queue: TreeSet<SimpleNode> = TreeSet(DFOComparator())

  private val orderCache = WeakIdentityHashMap<SimpleCFG, List<SimpleNode>>()
  private fun order(cfg: SimpleCFG): List<SimpleNode> {
    return orderCache.computeIfAbsent(cfg) { getDepthFirstOrderedNodes(it) }
  }

  fun process(cfg: SimpleCFG) {
    depthFirstOrder.clear()
    queue.clear()

    var count = 1
    for (node in order(cfg)) {
      depthFirstOrder[node] = count++
    }
  }

  fun add(node: SimpleNode) {
    queue.add(node)
  }

  fun poll(): SimpleNode? = queue.pollFirst()

  override fun toString() = "Worklist($queue)"
}
