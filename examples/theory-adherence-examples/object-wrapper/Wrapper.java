import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.*;


import java.util.function.Supplier;

@Typestate("Wrapper.protocol")
class Wrapper {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: State{JavaIterator, HasNext})
    // :: warning: (this.iterator: State{JavaIterator, Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: State{JavaIterator, Next})
    return iterator.next();
  }
}
