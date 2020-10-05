import org.checkerframework.checker.mungo.lib.MungoTypestate;
import org.checkerframework.checker.mungo.lib.MungoRequires;
import org.checkerframework.checker.mungo.lib.MungoNullable;

import java.util.function.Supplier;

class WrapperWithoutProtocol1 {

  // :: error: (Object did not complete its protocol. Type: JavaIterator{HasNext|Next} | Ended | Null | Moved)
  public @MungoNullable JavaIterator iterator = null;

  public WrapperWithoutProtocol1(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: JavaIterator{HasNext|Next})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Ended | Null | Moved)
    // :: error: (Cannot call hasNext on null, on ended protocol, on moved value)
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Ended | Null | Moved)
    // :: error: (Cannot call next on null, on ended protocol, on moved value, on state HasNext (got: HasNext, Next))
    return iterator.next();
  }

  private String privateNext() {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Ended | Null | Moved)
    // :: error: (Cannot call next on null, on ended protocol, on moved value, on state HasNext (got: HasNext, Next))
    return iterator.next();
  }

  public static void main() {
    WrapperWithoutProtocol1 wrapper = new WrapperWithoutProtocol1(new JavaIterator());
    // :: error: (Cannot call hasNext on null, on ended protocol, on moved value)
    wrapper.iterator.hasNext();
  }

}

class WrapperWithoutProtocol2 {

  // :: error: (Object did not complete its protocol. Type: JavaIterator{HasNext|Next} | Ended)
  private @MungoNullable JavaIterator iterator = null;

  public WrapperWithoutProtocol2(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: JavaIterator{HasNext|Next})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Ended)
    // :: error: (Cannot call hasNext on ended protocol)
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Ended)
    // :: error: (Cannot call next on ended protocol, on state HasNext (got: HasNext, Next))
    return iterator.next();
  }

  private String privateNext() {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Ended | Null | Moved)
    // :: error: (Cannot call next on null, on ended protocol, on moved value, on state HasNext (got: HasNext, Next))
    return iterator.next();
  }

}
