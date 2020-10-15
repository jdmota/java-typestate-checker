package org.checkerframework.checker.mungo.assertions

import com.sun.source.tree.ClassTree
import com.sun.source.tree.CompilationUnitTree
import com.sun.source.tree.VariableTree
import com.sun.tools.javac.code.Type
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.abstract_analysis.*
import org.checkerframework.checker.mungo.analysis.TypeIntroducer
import org.checkerframework.checker.mungo.typecheck.MungoUnknownType
import org.checkerframework.dataflow.cfg.ControlFlowGraph
import org.checkerframework.dataflow.cfg.node.Node

class AnalyzerResult : AbstractAnalyzerResult<Store, MutableStore>() {
  override fun getThen(): Store {
    TODO("Not yet implemented")
  }

  override fun getElse(): Store {
    TODO("Not yet implemented")
  }

  override fun getRegular(): Store {
    TODO("Not yet implemented")
  }

  override fun isRegular(): Boolean {
    TODO("Not yet implemented")
  }

  override fun getExceptionalStore(cause: Any): Store? {
    TODO("Not yet implemented")
  }
}

class MutableAnalyzerResult : AbstractMutableAnalyzerResult<Store, MutableStore, AnalyzerResult>() {
  override fun merge(result: AnalyzerResult) {
    TODO("Not yet implemented")
  }

  override fun mergeThenAndElse() {
    TODO("Not yet implemented")
  }

  override fun getThen(): Store {
    TODO("Not yet implemented")
  }

  override fun getElse(): Store {
    TODO("Not yet implemented")
  }

  override fun isRegular(): Boolean {
    TODO("Not yet implemented")
  }

  override fun getExceptionalStore(cause: Any): Store? {
    TODO("Not yet implemented")
  }
}

class MutableAnalyzerResultWithValue : AbstractMutableAnalyzerResultWithValue<StoreInfo, Store, MutableStore, AnalyzerResult>() {
  override fun merge(result: AnalyzerResult) {
    TODO("Not yet implemented")
  }

  override fun mergeThenAndElse() {
    TODO("Not yet implemented")
  }

  override fun getThen(): Store {
    TODO("Not yet implemented")
  }

  override fun getElse(): Store {
    TODO("Not yet implemented")
  }

  override fun isRegular(): Boolean {
    TODO("Not yet implemented")
  }

  override fun getExceptionalStore(cause: Any): Store? {
    TODO("Not yet implemented")
  }

  override fun getValue(): StoreInfo {
    TODO("Not yet implemented")
  }
}

class StoreInfo : AbstractStoreInfo()

class Store : AbstractStore<Store, MutableStore>() {
  override fun toMutable(): MutableStore {
    TODO("Not yet implemented")
  }

  override fun toImmutable(): Store {
    TODO("Not yet implemented")
  }
}

class MutableStore : AbstractMutableStore<Store, MutableStore>() {
  override fun toMutable(): MutableStore {
    TODO("Not yet implemented")
  }

  override fun toImmutable(): Store {
    TODO("Not yet implemented")
  }

  override fun merge(other: Store): MutableStore {
    TODO("Not yet implemented")
  }

  override fun mergeFields(other: Store): MutableStore {
    TODO("Not yet implemented")
  }

  override fun toBottom(): MutableStore {
    TODO("Not yet implemented")
  }

  override fun invalidate(analyzer: AbstractAnalyzerBase): MutableStore {
    TODO("Not yet implemented")
  }

  override fun invalidateFields(analyzer: AbstractAnalyzerBase): MutableStore {
    TODO("Not yet implemented")
  }

  override fun invalidatePublicFields(analyzer: AbstractAnalyzerBase): MutableStore {
    TODO("Not yet implemented")
  }
}

class StoreUtils : AbstractStoreUtils<Store, MutableStore>() {
  override fun emptyStore(): Store {
    TODO("Not yet implemented")
  }

  override fun mutableEmptyStore(): MutableStore {
    TODO("Not yet implemented")
  }

  override fun merge(a: Store, b: Store): Store {
    TODO("Not yet implemented")
  }

  override fun mutableMergeFields(a: Store, b: Store): MutableStore {
    TODO("Not yet implemented")
  }
}

class StoreInfoUtils : AbstractStoreInfoUtils<StoreInfo>() {
  override fun merge(a: StoreInfo, b: StoreInfo): StoreInfo {
    TODO("Not yet implemented")
  }

  override fun intersect(a: StoreInfo, b: StoreInfo): StoreInfo {
    TODO("Not yet implemented")
  }
}

class AnalyzerResultsUtils : AbstractAnalyzerResultUtils<StoreInfo, Store, MutableStore, AnalyzerResult, MutableAnalyzerResult, MutableAnalyzerResultWithValue>() {
  override fun createAnalyzerResult(thenStore: Store, elseStore: Store): AnalyzerResult {
    TODO("Not yet implemented")
  }

  override fun createAnalyzerResult(result: MutableAnalyzerResult): AnalyzerResult {
    TODO("Not yet implemented")
  }

  override fun createAnalyzerResult(): AnalyzerResult {
    TODO("Not yet implemented")
  }

  override fun createMutableAnalyzerResult(thenStore: MutableStore, elseStore: MutableStore): MutableAnalyzerResult {
    TODO("Not yet implemented")
  }

  override fun createMutableAnalyzerResult(): MutableAnalyzerResult {
    TODO("Not yet implemented")
  }

  override fun createMutableAnalyzerResultWithValue(value: StoreInfo, result: AnalyzerResult): MutableAnalyzerResultWithValue {
    TODO("Not yet implemented")
  }
}

class Inferrer(checker: MungoChecker) : AbstractAnalyzer<
  AnalyzerResult,
  MutableAnalyzerResult,
  MutableAnalyzerResultWithValue,
  StoreInfo,
  Store,
  MutableStore,
  StoreUtils,
  StoreInfoUtils,
  AnalyzerResultsUtils
  >(checker, StoreUtils(), StoreInfoUtils(), AnalyzerResultsUtils()) {
  override fun setRoot(root: CompilationUnitTree) {
    super.setRoot(root)
  }

  override fun getInitialInfo(node: Node): StoreInfo {
    TODO("Not yet implemented")
  }

  override fun handleUninitializedField(store: MutableStore, field: VariableTree, ct: ClassTree) {
    TODO("Not yet implemented")
  }

  override fun initialStore(capturedStore: Store, cfg: ControlFlowGraph): Store {
    TODO("Not yet implemented")
  }

  override fun visit(node: Node, mutableResult: MutableAnalyzerResultWithValue) {
    TODO("Not yet implemented")
  }
}
