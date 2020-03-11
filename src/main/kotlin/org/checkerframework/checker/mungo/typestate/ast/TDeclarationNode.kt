package org.checkerframework.checker.mungo.typestate.ast

class TDeclarationNode(pos: Position, val name: String, val states: List<TStateNode>) : TNode(pos)
