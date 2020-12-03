package utils;

import org.checkerframework.checker.jtc.lib.Typestate;
import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIterator.protocol")
public class JavaIterator {

  public boolean hasNext() {
    return false;
  }

  public String next() {
    return "";
  }

}
