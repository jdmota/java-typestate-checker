package org.checkerframework.checker.mungo

import org.checkerframework.checker.mungo.typecheck.MungoVisitor
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.common.basetype.BaseTypeChecker
import org.checkerframework.common.basetype.BaseTypeVisitor
import org.checkerframework.javacutil.trees.TreeBuilder

/**
 * This is the entry point for pluggable type-checking.
 */
class MungoChecker : BaseTypeChecker() {

  private lateinit var utils: MungoUtils;

  fun getUtils(): MungoUtils {
    if (!this::utils.isInitialized) {
      utils = MungoUtils(this)
    }
    return utils
  }

  private lateinit var builder: TreeBuilder;

  fun getBuilder(): TreeBuilder {
    if (!this::builder.isInitialized) {
      builder = TreeBuilder(processingEnv)
    }
    return builder
  }

  override fun createSourceVisitor(): BaseTypeVisitor<*> {
    return MungoVisitor(this)
  }
}
