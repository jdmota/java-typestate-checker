package org.checkerframework.checker.mungo.abstract_analysis

abstract class AbstractStoreInfo

abstract class AbstractStoreInfoUtils<StoreInfo: AbstractStoreInfo> {
  abstract fun merge(a: StoreInfo, b: StoreInfo): StoreInfo
  abstract fun intersect(a: StoreInfo, b: StoreInfo): StoreInfo
}

abstract class AbstractStore<Store: AbstractStore<Store, MutableStore>, MutableStore: AbstractMutableStore<Store, MutableStore>> {
  abstract fun toMutable(): MutableStore
  abstract fun toImmutable(): Store
}

abstract class AbstractMutableStore<Store: AbstractStore<Store, MutableStore>, MutableStore: AbstractMutableStore<Store, MutableStore>> : AbstractStore<Store, MutableStore>() {
  abstract fun merge(other: Store): MutableStore
  abstract fun mergeFields(other: Store): MutableStore
  abstract fun toBottom(): MutableStore
  abstract fun invalidate(analyzer: AbstractAnalyzerBase): MutableStore
  abstract fun invalidateFields(analyzer: AbstractAnalyzerBase): MutableStore
  abstract fun invalidatePublicFields(analyzer: AbstractAnalyzerBase): MutableStore
}

abstract class AbstractStoreUtils<Store: AbstractStore<Store, MutableStore>, MutableStore: AbstractMutableStore<Store, MutableStore>> {
  abstract fun emptyStore(): Store
  abstract fun mutableEmptyStore(): MutableStore
  abstract fun merge(a: Store, b: Store): Store
  abstract fun mutableMergeFields(a: Store, b: Store): MutableStore
}

