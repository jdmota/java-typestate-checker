package org.checkerframework.checker.jtc.core.cfg

import java.util.*

// This file includes the implementation of a simplified version of Checker's CFG
// Differences:
// - Does not include blocks, only nodes
// - Includes a BOTH_TO_BOTH flow rule
// This allows for our analysis to be simple and more independent from Checker,
// potentially allowing for our type system to be employed in other languages.

enum class SimpleFlowRule {
  EACH_TO_EACH,
  THEN_TO_BOTH,
  ELSE_TO_BOTH,
  THEN_TO_THEN,
  ELSE_TO_ELSE,
  BOTH_TO_THEN,
  BOTH_TO_ELSE,
  BOTH_TO_BOTH
}

class SimpleEdge(val rule: SimpleFlowRule, val node: SimpleNode) {
  operator fun component1() = rule
  operator fun component2() = node
}

sealed class SimpleNode {
  val outEdges = mutableListOf<SimpleEdge>()

  fun addOutEdge(edge: SimpleEdge) {
    outEdges.add(edge)
  }
}

sealed class SimpleMarker : SimpleNode()
class SimpleMarkerEntry : SimpleMarker()
class SimpleMarkerExit : SimpleMarker()

class SimpleCodeNode(val code: CodeExpr) : SimpleNode() {
  var isCondition: Boolean = false

  override fun toString(): String {
    return code.toString()
  }
}

class SimpleCFG(
  val entry: SimpleMarkerEntry = SimpleMarkerEntry(),
  val exit: SimpleMarkerExit = SimpleMarkerExit(),
  val allNodes: MutableList<SimpleNode> = mutableListOf(entry, exit)
)

fun joinCFGs(list: Collection<SimpleCFG>): SimpleCFG {
  val allNodes = mutableListOf<SimpleNode>()
  val iterator = list.iterator()
  val first = iterator.next()
  val entry = first.entry
  var last = first.exit
  allNodes.addAll(first.allNodes)
  while (iterator.hasNext()) {
    val next = iterator.next()
    last.addOutEdge(SimpleEdge(SimpleFlowRule.BOTH_TO_BOTH, next.entry))
    last = next.exit
    allNodes.addAll(next.allNodes)
  }
  return SimpleCFG(entry, last, allNodes)
}

fun createOneExprCFG(expr: CodeExpr): SimpleCFG {
  val entry = SimpleMarkerEntry()
  val node = SimpleCodeNode(expr)
  val exit = SimpleMarkerExit()
  entry.addOutEdge(SimpleEdge(SimpleFlowRule.BOTH_TO_BOTH, node))
  node.addOutEdge(SimpleEdge(SimpleFlowRule.BOTH_TO_BOTH, exit))
  return SimpleCFG(entry, exit, mutableListOf(node))
}

fun getDepthFirstOrderedNodes(cfg: SimpleCFG): List<SimpleNode> {
  val dfsOrderResult = mutableListOf<SimpleNode>()
  val visited = mutableSetOf<SimpleNode>()
  val worklist = ArrayDeque<SimpleNode>()
  worklist.add(cfg.entry)
  while (!worklist.isEmpty()) {
    val cur = worklist.last
    if (visited.contains(cur)) {
      dfsOrderResult.add(cur)
      worklist.removeLast()
    } else {
      visited.add(cur)
      for ((_, node) in cur.outEdges) {
        if (!visited.contains(node)) {
          worklist.add(node)
        }
      }
    }
  }
  dfsOrderResult.reverse()
  return dfsOrderResult
}
