package org.checkerframework.checker.jtc.lib;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

// Use: @State("Next")

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.LOCAL_VARIABLE, ElementType.PARAMETER, ElementType.TYPE_USE})
public @interface State {
  String[] value();
}
