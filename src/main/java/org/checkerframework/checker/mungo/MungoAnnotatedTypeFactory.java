package org.checkerframework.checker.mungo;

import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;

public class MungoAnnotatedTypeFactory extends BaseAnnotatedTypeFactory {
  public MungoAnnotatedTypeFactory(BaseTypeChecker checker) {
    super(checker);
    this.postInit();
  }
}
