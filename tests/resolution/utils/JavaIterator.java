package utils;

import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Nullable;

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
