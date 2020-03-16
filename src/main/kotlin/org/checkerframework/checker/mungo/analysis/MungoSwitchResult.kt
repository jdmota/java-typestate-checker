package org.checkerframework.checker.mungo.analysis

import org.checkerframework.dataflow.analysis.TransferResult
import java.util.*
import javax.lang.model.type.TypeMirror

class MungoSwitchResult(
  private val store: MungoStore,
  private val storeChanged: Boolean,
  private val caseStores: Map<TypeMirror, MungoStore>,
  resultValue: MungoValue?,
  exceptionalStores: Map<TypeMirror, MungoStore>?
) : TransferResult<MungoValue, MungoStore>(resultValue, exceptionalStores) {

  override fun getRegularStore(): MungoStore {
    return store
  }

  override fun getThenStore(): MungoStore {
    return store
  }

  override fun getElseStore(): MungoStore {
    // copy the store such that it is the same as the result of getThenStore
    // (that is, identical according to equals), but two different objects.
    return store.copy()
  }

  override fun containsTwoStores(): Boolean {
    return false
  }

  override fun toString(): String {
    val result = StringJoiner(System.lineSeparator())
    result.add("MungoSwitchResult(")
    result.add("  resultValue = $resultValue")
    result.add("  store = $store")
    result.add(")")
    return result.toString()
  }

  override fun storeChanged(): Boolean {
    return storeChanged
  }

}
