package org.checkerframework.checker.jtc.analysis

import org.checkerframework.dataflow.cfg.ControlFlowGraph
import org.checkerframework.dataflow.cfg.block.Block
import java.util.*

// Adapted from org.checkerframework.dataflow.analysis.Analysis.Worklist

class Worklist {
  private val depthFirstOrder: IdentityHashMap<Block, Int> = IdentityHashMap()

  inner class DFOComparator : Comparator<Block> {
    override fun compare(b1: Block, b2: Block): Int {
      return depthFirstOrder[b1]!! - depthFirstOrder[b2]!!
    }
  }

  private val queue: TreeSet<Block> = TreeSet(DFOComparator())

  fun process(cfg: ControlFlowGraph) {
    depthFirstOrder.clear()
    queue.clear()

    var count = 1
    for (b in cfg.depthFirstOrderedBlocks) {
      depthFirstOrder[b] = count++
    }
  }

  fun add(block: Block) {
    queue.add(block)
  }

  fun poll(): Block? = queue.pollFirst()

  override fun toString() = "Worklist($queue)"
}
