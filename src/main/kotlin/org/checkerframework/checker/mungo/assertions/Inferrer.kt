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

val storeUtils = StoreUtils()
val storeInfoUtils = StoreInfoUtils()
val analyzerResultsUtils = AnalyzerResultsUtils()

class AnalyzerResult(
  private val thenStore: Store,
  private val elseStore: Store
) : AbstractAnalyzerResult<Store, MutableStore>() {

  private val regularStore = storeUtils.merge(thenStore, elseStore)

  constructor(thenStore: MutableStore, elseStore: MutableStore) : this(thenStore.toImmutable(), elseStore.toImmutable())
  constructor(result: MutableAnalyzerResult) : this(result.getThen().toImmutable(), result.getElse().toImmutable())

  override fun getThen(): Store = thenStore
  override fun getElse(): Store = elseStore
  override fun getRegular(): Store = regularStore
  override fun isRegular(): Boolean = thenStore === elseStore

  override fun getExceptionalStore(cause: Any): Store? {
    return null // TODO
  }

  override fun toString(): String {
    if (isRegular()) {
      return "Result{store=$thenStore}"
    }
    return "Result{\nthen=$thenStore,\nelse=$elseStore\n}"
  }
}

class MutableAnalyzerResult(
  private var thenStore: MutableStore,
  private var elseStore: MutableStore
) : AbstractMutableAnalyzerResult<Store, MutableStore, AnalyzerResult>() {
  override fun merge(result: AnalyzerResult) {
    thenStore.merge(result.getThen())
    if (!isRegular() || !result.isRegular()) {
      elseStore.merge(result.getElse())
    }
  }

  override fun mergeThenAndElse() {
    thenStore.merge(elseStore)
    elseStore = thenStore
  }

  override fun getThen(): MutableStore = thenStore
  override fun getElse(): MutableStore = elseStore
  override fun isRegular(): Boolean = thenStore === elseStore

  override fun getExceptionalStore(cause: Any): MutableStore? {
    return null // TODO
  }

  override fun toString(): String {
    if (isRegular()) {
      return "Result{store=$thenStore}"
    }
    return "Result{\nthen=$thenStore,\nelse=$elseStore\n}"
  }
}

class MutableAnalyzerResultWithValue(
  private var value: StoreInfo,
  private var thenStore: MutableStore,
  private var elseStore: MutableStore
) : AbstractMutableAnalyzerResultWithValue<StoreInfo, Store, MutableStore, AnalyzerResult>() {
  override fun merge(result: AnalyzerResult) {
    thenStore.merge(result.getThen())
    if (!isRegular() || !result.isRegular()) {
      elseStore.merge(result.getElse())
    }
  }

  override fun mergeThenAndElse() {
    thenStore.merge(elseStore)
    elseStore = thenStore
  }

  override fun getThen(): MutableStore = thenStore
  override fun getElse(): MutableStore = elseStore
  override fun isRegular(): Boolean = thenStore === elseStore

  override fun getExceptionalStore(cause: Any): MutableStore? {
    return null // TODO
  }

  override fun toString(): String {
    if (isRegular()) {
      return "Result{value=$value, store=$thenStore}"
    }
    return "Result{value=$value,\nthen=$thenStore,\nelse=$elseStore\n}"
  }

  override fun getValue() = value
  override fun setValue(v: StoreInfo) {
    value = v
  }
}

class StoreInfo : AbstractStoreInfo()

open class Store : AbstractStore<Store, MutableStore>() {
  override fun toMutable(): MutableStore {
    TODO("Not yet implemented")
  }

  override fun toImmutable(): Store {
    return this
  }
}

class MutableStore : AbstractMutableStore<Store, MutableStore>() {
  override fun toMutable(): MutableStore {
    TODO("Not yet implemented")
  }

  override fun toImmutable(): Store {
    TODO("Not yet implemented")
  }

  override fun merge(other: Store) {
    TODO("Not yet implemented")
  }

  override fun mergeFields(other: Store) {
    TODO("Not yet implemented")
  }

  override fun merge(other: MutableStore) {
    TODO("Not yet implemented")
  }

  override fun mergeFields(other: MutableStore) {
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
    return AnalyzerResult(thenStore, elseStore)
  }

  override fun createAnalyzerResult(thenStore: MutableStore, elseStore: MutableStore): AnalyzerResult {
    return AnalyzerResult(thenStore, elseStore)
  }

  override fun createAnalyzerResult(result: MutableAnalyzerResult): AnalyzerResult {
    return createAnalyzerResult(result.getThen(), result.getElse())
  }

  override fun createAnalyzerResult(): AnalyzerResult {
    return createAnalyzerResult(storeUtils.emptyStore(), storeUtils.emptyStore())
  }

  override fun createMutableAnalyzerResult(thenStore: MutableStore, elseStore: MutableStore): MutableAnalyzerResult {
    return MutableAnalyzerResult(thenStore, elseStore)
  }

  override fun createMutableAnalyzerResult(): MutableAnalyzerResult {
    return createMutableAnalyzerResult(storeUtils.mutableEmptyStore(), storeUtils.mutableEmptyStore())
  }

  override fun createMutableAnalyzerResultWithValue(value: StoreInfo, result: AnalyzerResult): MutableAnalyzerResultWithValue {
    return MutableAnalyzerResultWithValue(value, result.getThen().toMutable(), result.getElse().toMutable())
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
