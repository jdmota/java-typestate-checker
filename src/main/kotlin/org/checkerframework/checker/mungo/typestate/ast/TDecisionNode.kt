package org.checkerframework.checker.mungo.typestate.ast

class TDecisionNode(pos: Position, val label: String, /*TIdNode | TStateNode*/val destination: TNode) : TNode(pos)
