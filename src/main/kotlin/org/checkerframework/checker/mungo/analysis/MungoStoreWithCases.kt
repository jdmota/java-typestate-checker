package org.checkerframework.checker.mungo.analysis

import org.checkerframework.dataflow.cfg.CFGVisualizer
import java.lang.AssertionError
import java.lang.StringBuilder

// Since "TransferResult"'s are always given to the next transfer function via "TransferInput",
// which only expects a regular store or a then/else store pair,
// we save each store for each "case" inside our store.
// This seems like an hack but it works.
// Ideally, Checker should support different "TransferResult"'s.

class MungoStoreWithCases : MungoStore {
  constructor(caseStores: Map<String, MungoStore>, other: MungoStore) : super(other) {
    if (caseStores.isEmpty()) throw AssertionError("MungoStoreWithCases: empty caseStores")
    if (other is MungoStoreWithCases) throw AssertionError("MungoStoreWithCases: other is MungoStoreWithCases")
    this.caseStores = caseStores
  }

  // This will be called when copying
  constructor(other: MungoStoreWithCases) : super(other) {
    this.caseStores = HashMap(other.caseStores)
  }

  val caseStores: Map<String, MungoStore>

  override fun internalVisualize(viz: CFGVisualizer<MungoValue, MungoStore, *>): String {
    val builder = StringBuilder()
    builder.append(super.internalVisualize(viz))
    builder.append("-- cases --\n")
    for ((label, store) in caseStores) {
      builder.append("case $label: $store\n")
    }
    return builder.toString()
  }
}
