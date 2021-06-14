import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Nullable;

import java.util.function.Supplier;

import utils.JavaIterator;

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper1 {

  private JavaIterator iterator;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{utils.JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: State{utils.JavaIterator, HasNext} | State{utils.JavaIterator, Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: State{utils.JavaIterator, Next})
    return iterator.next();
  }

}
