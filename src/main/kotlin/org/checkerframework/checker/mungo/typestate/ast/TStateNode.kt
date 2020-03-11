package org.checkerframework.checker.mungo.typestate.ast

class TStateNode(pos: Position, val name: String?, val methods: List<TMethodNode>) : TNode(pos)
