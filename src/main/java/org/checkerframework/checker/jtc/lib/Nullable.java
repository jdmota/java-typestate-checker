package org.checkerframework.checker.jtc.lib;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.LOCAL_VARIABLE, ElementType.PARAMETER, ElementType.TYPE_USE, ElementType.TYPE_PARAMETER, ElementType.FIELD})
public @interface Nullable {

}
