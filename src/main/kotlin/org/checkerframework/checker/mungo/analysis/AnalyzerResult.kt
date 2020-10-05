package org.checkerframework.checker.mungo.analysis

class AnalyzerResult(_thenStore: Store, _elseStore: Store) {

  val thenStore = _thenStore.toImmutable()
  val elseStore = _elseStore.toImmutable()
  val regularStore = Store.merge(thenStore, elseStore)

  constructor(result: MutableAnalyzerResult) : this(result.thenStore, result.elseStore)

  fun isRegular() = thenStore === elseStore

  fun getExceptionalStore(cause: Any): Store? {
    return null // TODO
  }

  override fun toString(): String {
    if (isRegular()) {
      return "Result{store=$thenStore}"
    }
    return "Result{\nthen=$thenStore,\nelse=$elseStore\n}"
  }

}

open class MutableAnalyzerResult(var thenStore: MutableStore, var elseStore: MutableStore) {

  fun isRegular() = thenStore === elseStore

  fun merge(result: AnalyzerResult) {
    thenStore.merge(result.thenStore)
    if (!isRegular() || !result.isRegular()) {
      elseStore.merge(result.elseStore)
    }
  }

  fun mergeThenAndElse() {
    thenStore.merge(elseStore)
    elseStore = thenStore
  }

  fun getInfo(ref: Reference): StoreInfo? {
    val a = thenStore[ref]
    val b = elseStore[ref]
    if (a === null) return b
    if (b === null) return a
    return StoreInfo.merge(a, b)
  }

  fun getExceptionalStore(cause: Any): Store? {
    return null // TODO
  }

  override fun toString(): String {
    if (isRegular()) {
      return "Result{store=$thenStore}"
    }
    return "Result{\nthen=$thenStore,\nelse=$elseStore\n}"
  }

}

class MutableAnalyzerResultWithValue(var value: StoreInfo, thenStore: MutableStore, elseStore: MutableStore) : MutableAnalyzerResult(thenStore, elseStore) {

  constructor(value: StoreInfo, result: AnalyzerResult) : this(value, result.thenStore.toMutable(), result.elseStore.toMutable())

  override fun toString(): String {
    if (isRegular()) {
      return "Result{value=$value, store=$thenStore}"
    }
    return "Result{value=$value,\nthen=$thenStore,\nelse=$elseStore\n}"
  }

}
