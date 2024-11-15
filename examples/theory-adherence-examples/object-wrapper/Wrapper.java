import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.*;


import java.util.function.Supplier;

@Typestate("Iterator.protocol")
class Wrapper {

  private @Nullable JavaIterator iterator = null;

  public Wrapper() {
    iterator = new JavaIterator();
  }

  public boolean hasNext() {
    return iterator.hasNext();
  }

  public String next() {
    return iterator.next();
  }
}
