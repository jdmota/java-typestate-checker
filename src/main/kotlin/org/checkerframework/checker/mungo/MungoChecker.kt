package org.checkerframework.checker.mungo

import org.checkerframework.checker.mungo.typecheck.MungoVisitor
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.common.basetype.BaseTypeChecker
import org.checkerframework.common.basetype.BaseTypeVisitor

const val showTypeInfoOpt = "showTypeInfo"

/**
 * This is the entry point for pluggable type-checking.
 */
class MungoChecker : BaseTypeChecker() {

  private lateinit var _utils: MungoUtils
  val utils: MungoUtils
    get() {
      if (!this::_utils.isInitialized) {
        _utils = MungoUtils(this)
      }
      return _utils
    }

  override fun createSourceVisitor(): BaseTypeVisitor<*> {
    return MungoVisitor(this)
  }

  override fun getSupportedOptions() = super.getSupportedOptions().plus(showTypeInfoOpt)

  fun shouldReportTypeInfo() = hasOption(showTypeInfoOpt)
}
