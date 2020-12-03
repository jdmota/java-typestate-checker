package org.checkerframework.checker.jtc.lib;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

// Use: @Typestate("FileProtocol.protocol")

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE})
public @interface Typestate {
  String value();
}
