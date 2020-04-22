package org.checkerframework.checker.mungo.lib;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

// Use: @MungoTypestate("FileProtocol.protocol")

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE})
public @interface MungoTypestate {
  String value();
}
