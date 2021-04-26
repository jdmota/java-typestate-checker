import org.checkerframework.checker.jtc.lib.Typestate;
import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.Nullable;

class WrapperWithoutProtocol1 {

  // :: error: (Object did not complete its protocol. Type: State "HasNext" | State "Next" | Ended | Null | Moved)
  public @Nullable JavaIterator iterator = null;

  public WrapperWithoutProtocol1(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: State "HasNext" | State "Next")
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (iterator: State "HasNext" | State "Next" | Ended | Null | Moved)
    // :: error: (Cannot call hasNext on null, on ended protocol, on moved value)
    // :: error: (Access of object with protocol inside object without protocol might break linearity)
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: State "HasNext" | State "Next" | Ended | Null | Moved)
    // :: error: (Cannot call next on null, on ended protocol, on moved value, on state HasNext (got: HasNext, Next))
    // :: error: (Access of object with protocol inside object without protocol might break linearity)
    return iterator.next();
  }

  private String privateNext() {
    // :: warning: (iterator: State "HasNext" | State "Next" | Ended | Null | Moved)
    // :: error: (Cannot call next on null, on ended protocol, on moved value, on state HasNext (got: HasNext, Next))
    // :: error: (Access of object with protocol inside object without protocol might break linearity)
    return iterator.next();
  }

  public static void main() {
    WrapperWithoutProtocol1 wrapper = new WrapperWithoutProtocol1(new JavaIterator());
    // :: error: (Cannot call hasNext on unknown)
    wrapper.iterator.hasNext();
  }

}

class WrapperWithoutProtocol2 {

  // :: error: (Object did not complete its protocol. Type: State "HasNext" | State "Next" | Ended)
  private @Nullable JavaIterator iterator = null;

  public WrapperWithoutProtocol2(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: State "HasNext" | State "Next")
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (iterator: State "HasNext" | State "Next" | Ended)
    // :: error: (Cannot call hasNext on ended protocol)
    // :: error: (Access of object with protocol inside object without protocol might break linearity)
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: State "HasNext" | State "Next" | Ended)
    // :: error: (Cannot call next on ended protocol, on state HasNext (got: HasNext, Next))
    // :: error: (Access of object with protocol inside object without protocol might break linearity)
    return iterator.next();
  }

  private String privateNext() {
    // :: warning: (iterator: State "HasNext" | State "Next" | Ended | Null | Moved)
    // :: error: (Cannot call next on null, on ended protocol, on moved value, on state HasNext (got: HasNext, Next))
    // :: error: (Access of object with protocol inside object without protocol might break linearity)
    return iterator.next();
  }

}
