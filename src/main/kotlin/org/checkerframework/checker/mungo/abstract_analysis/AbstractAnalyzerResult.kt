package org.checkerframework.checker.mungo.abstract_analysis

abstract class AbstractAnalyzerResult<Store : AbstractStore<Store, MutableStore>, MutableStore : AbstractMutableStore<Store, MutableStore>> {
  abstract fun getThen(): Store
  abstract fun getElse(): Store
  abstract fun getRegular(): Store
  abstract fun isRegular(): Boolean
  abstract fun getExceptionalStore(cause: Any): Store?
}

abstract class AbstractMutableAnalyzerResult<Store : AbstractStore<Store, MutableStore>, MutableStore : AbstractMutableStore<Store, MutableStore>, AnalyzerResult : AbstractAnalyzerResult<Store, MutableStore>> {
  abstract fun merge(result: AnalyzerResult)
  abstract fun mergeThenAndElse()
  abstract fun getThen(): MutableStore
  abstract fun getElse(): MutableStore
  abstract fun isRegular(): Boolean
  abstract fun getExceptionalStore(cause: Any): MutableStore?
}

abstract class AbstractMutableAnalyzerResultWithValue<StoreInfo : AbstractStoreInfo, Store : AbstractStore<Store, MutableStore>, MutableStore : AbstractMutableStore<Store, MutableStore>, AnalyzerResult : AbstractAnalyzerResult<Store, MutableStore>> : AbstractMutableAnalyzerResult<Store, MutableStore, AnalyzerResult>() {
  abstract fun getValue(): StoreInfo
  abstract fun setValue(v: StoreInfo)
}

abstract class AbstractAnalyzerResultUtils<
  StoreInfo : AbstractStoreInfo,
  Store : AbstractStore<Store, MutableStore>,
  MutableStore : AbstractMutableStore<Store, MutableStore>,
  AnalyzerResult : AbstractAnalyzerResult<Store, MutableStore>,
  MutableAnalyzerResult : AbstractMutableAnalyzerResult<Store, MutableStore, AnalyzerResult>,
  MutableAnalyzerResultWithValue : AbstractMutableAnalyzerResultWithValue<StoreInfo, Store, MutableStore, AnalyzerResult>
  > {
  abstract fun createAnalyzerResult(thenStore: MutableStore, elseStore: MutableStore): AnalyzerResult
  abstract fun createAnalyzerResult(thenStore: Store, elseStore: Store): AnalyzerResult
  abstract fun createAnalyzerResult(result: MutableAnalyzerResult): AnalyzerResult
  abstract fun createAnalyzerResult(): AnalyzerResult
  abstract fun createMutableAnalyzerResult(thenStore: MutableStore, elseStore: MutableStore): MutableAnalyzerResult
  abstract fun createMutableAnalyzerResult(): MutableAnalyzerResult
  abstract fun createMutableAnalyzerResultWithValue(value: StoreInfo, result: AnalyzerResult): MutableAnalyzerResultWithValue
}
