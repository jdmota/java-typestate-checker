package jatyc.core.cfg

import jatyc.core.SelectReference
import java.util.*

// This file includes the implementation of a simplified version of Checker's CFG
// Differences:
// - Does not include blocks, only nodes
// - Flow rules are simpler
// This allows for our analysis to be simple and more independent of Checker,
// potentially allowing for our type system to be employed in other languages.

enum class SimpleFlowRule {
  THEN, ELSE, ALL
}

class SimpleEdge(val rule: SimpleFlowRule, val to: SimpleNode, val backEdge: Boolean)

sealed class SimpleNode {
  val outEdges = mutableListOf<SimpleEdge>()

  fun addOutEdge(edge: SimpleEdge) {
    outEdges.add(edge)
  }

  var isCondition: Boolean = false
  var isLoopEntry: Boolean = false
  var isInsideLoop: Boolean = false

  abstract fun format(): String
}

sealed class SimpleMarker : SimpleNode() {
  override fun format() = toString()
}
class SimpleMarkerEntry : SimpleMarker()
class SimpleMarkerExit : SimpleMarker()

class SimpleCodeNode(val code: CodeExpr) : SimpleNode() {
  override fun toString(): String {
    return code.toString()
  }

  override fun format() = code.format()
}

class SimpleCFG(
  val entry: SimpleMarkerEntry = SimpleMarkerEntry(),
  val exit: SimpleMarkerExit = SimpleMarkerExit(),
  val allNodes: MutableList<SimpleNode> = mutableListOf(entry, exit)
) {
  lateinit var detailedInfo: DetailedCFGInfo
}

open class DetailedCFGInfo(
  val potentiallyModified: MutableSet<SelectReference> = mutableSetOf(),
  val innerCalls: MutableSet<MethodCall> = mutableSetOf()
) {
  fun addAll(info: DetailedCFGInfo) {
    potentiallyModified.addAll(info.potentiallyModified)
    innerCalls.addAll(info.innerCalls)
  }
}

fun joinCFGs(list: Collection<SimpleCFG>): SimpleCFG {
  val info = DetailedCFGInfo()
  val allNodes = mutableListOf<SimpleNode>()
  val iterator = list.iterator()
  val first = iterator.next()
  val entry = first.entry
  var last = first.exit
  allNodes.addAll(first.allNodes)
  info.addAll(first.detailedInfo)
  while (iterator.hasNext()) {
    val next = iterator.next()
    last.addOutEdge(SimpleEdge(SimpleFlowRule.ALL, next.entry, false))
    last = next.exit
    allNodes.addAll(next.allNodes)
    info.addAll(next.detailedInfo)
  }
  val cfg = SimpleCFG(entry, last, allNodes)
  cfg.detailedInfo = info
  return cfg
}

fun createOneExprCFG(expr: CodeExpr): SimpleCFG {
  val entry = SimpleMarkerEntry()
  val node = SimpleCodeNode(expr)
  val exit = SimpleMarkerExit()
  entry.addOutEdge(SimpleEdge(SimpleFlowRule.ALL, node, false))
  node.addOutEdge(SimpleEdge(SimpleFlowRule.ALL, exit, false))
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
      for (edge in cur.outEdges) {
        if (!visited.contains(edge.to)) {
          worklist.add(edge.to)
        }
      }
    }
  }
  dfsOrderResult.reverse()
  return dfsOrderResult
}
