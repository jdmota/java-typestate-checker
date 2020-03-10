package org.checkerframework.checker.mungo;

import org.checkerframework.checker.mungo.typecheck.MungoVisitor;
import org.checkerframework.checker.mungo.utils.MungoUtils;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;

/**
 * This is the entry point for pluggable type-checking.
 */
public class MungoChecker extends BaseTypeChecker {

  private MungoUtils utils = null;

  public MungoUtils getUtils() {
    return utils == null ? (utils = new MungoUtils(this)) : utils;
  }

  @Override
  protected BaseTypeVisitor<?> createSourceVisitor() {
    return new MungoVisitor(this);
  }
}
