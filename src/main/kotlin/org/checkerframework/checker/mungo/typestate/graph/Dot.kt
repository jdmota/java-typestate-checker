package org.checkerframework.checker.mungo.typestate.graph

import org.checkerframework.checker.mungo.typestate.graph.states.AbstractState
import org.checkerframework.checker.mungo.typestate.graph.states.DecisionState
import org.checkerframework.checker.mungo.typestate.graph.states.EndState
import org.checkerframework.checker.mungo.typestate.graph.states.State
import java.util.*

class Dot private constructor(private val graph: Graph) {
  private var decisionUuid = 1
  private var stateUuid = 1
  private val names: MutableMap<AbstractState<*, *>, String?>
  private val builder: StringBuilder

  // TODO prefer queue instead of recursion?
  private fun handleState(s: AbstractState<*, *>): String? {
    if (s is EndState) {
      return "end"
    }
    var name = names[s]
    if (name != null) {
      // Already saw this state
      return name
    }
    if (s is DecisionState) {
      name = "decision__" + decisionUuid++
      names[s] = name
      builder.append(name).append("[shape=\"diamond\"]\n")
      for ((key, value) in s.transitions) {
        val dest = handleState(value)
        builder.append(name).append(" -> ").append(dest).append("[label=\"").append(key.label).append("\"]\n")
      }
      return name
    }
    if (s is State) {
      val state = s
      name = if (state.node!!.name == null) "state__" + stateUuid++ else state.node!!.name
      names[s] = name
      for ((key, value) in state.transitions) {
        val dest = handleState(value)
        builder.append(name).append(" -> ").append(dest).append("[label=\"").append(key.name).append("\\(...\\)\"]\n")
      }
      return name
    }
    throw AssertionError("wrong state")
  }

  private fun gen(): String {
    builder.append("digraph {\n")
    val name = handleState(graph.getInitialState())
    builder.append("start").append("[shape=\"rectangle\"]\n")
    builder.append("start").append(" -> ").append(name).append("\n")
    builder.append("}\n")
    return builder.toString()
  }

  companion object {
    fun fromGraph(g: Graph): String {
      return Dot(g).gen()
    }
  }

  init {
    names = HashMap()
    builder = StringBuilder()
  }
}
