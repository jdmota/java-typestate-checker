package org.checkerframework.checker.mungo.typestate.graph.states

import org.checkerframework.checker.mungo.typestate.ast.TMethodNode
import org.checkerframework.checker.mungo.typestate.ast.TStateNode

open class State : AbstractState<TStateNode, TMethodNode> {
  var name: String

  protected constructor(name: String) : super(null) {
    this.name = name
  }

  constructor(node: TStateNode?) : super(node) {
    name = (if (node == null) "unknown" else node.name)!!
  }

  override fun toString(): String {
    return "State{name=$name,node=$node}"
  }
}
