package org.checkerframework.checker.mungo.typestate.graph.states

import org.checkerframework.checker.mungo.typestate.ast.TNode

// TODO check duplicate transitions and stuff...

abstract class AbstractState<N : TNode>(var node: N?) {

}
