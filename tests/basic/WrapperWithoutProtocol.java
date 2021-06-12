import org.checkerframework.checker.jtc.lib.Typestate;
import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.Nullable;

// :: error: ([this.iterator] did not complete its protocol (found: Shared{JavaIterator} | State{JavaIterator, ?}))
class WrapperWithoutProtocol1 {

  public JavaIterator iterator;

  public WrapperWithoutProtocol1(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: Shared{JavaIterator})
    // :: error: (Cannot call [hasNext] on Shared{JavaIterator})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: Shared{JavaIterator})
    // :: error: (Cannot call [next] on Shared{JavaIterator})
    return iterator.next();
  }

  private String privateNext() {
    // :: warning: (this.iterator: Shared{JavaIterator})
    // :: error: (Cannot call [next] on Shared{JavaIterator})
    return iterator.next();
  }

  public static void main() {
    WrapperWithoutProtocol1 wrapper = new WrapperWithoutProtocol1(new JavaIterator());
    // :: warning: (wrapper: NoProtocol{WrapperWithoutProtocol1, exact=true})
    // :: warning: (wrapper.iterator: Unknown)
    // :: error: (Cannot access [wrapper.iterator])
    wrapper.iterator.hasNext();
  }

}

// :: error: ([this.iterator] did not complete its protocol (found: Shared{JavaIterator} | State{JavaIterator, ?}))
class WrapperWithoutProtocol2 {

  private JavaIterator iterator;

  public WrapperWithoutProtocol2(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: Shared{JavaIterator})
    // :: error: (Cannot call [hasNext] on Shared{JavaIterator})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: Shared{JavaIterator})
    // :: error: (Cannot call [next] on Shared{JavaIterator})
    return iterator.next();
  }

  private String privateNext() {
    // :: warning: (this.iterator: Shared{JavaIterator})
    // :: error: (Cannot call [next] on Shared{JavaIterator})
    return iterator.next();
  }

}
