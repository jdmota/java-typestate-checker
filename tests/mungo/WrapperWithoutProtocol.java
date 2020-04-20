import org.checkerframework.checker.mungo.lib.MungoTypestate;
import org.checkerframework.checker.mungo.lib.MungoState;
import org.checkerframework.checker.mungo.lib.MungoNullable;

import java.util.function.Supplier;

class WrapperWithoutProtocol1 {

  public @MungoNullable JavaIterator iterator = null;

  public WrapperWithoutProtocol1(JavaIterator it) {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Null)
    // :: warning: (it: JavaIterator{HasNext|Next})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Ended | Moved | Null)
    // :: error: (Cannot call hasNext on null, on ended protocol, on moved value)
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Ended | Moved | Null)
    // :: error: (Cannot call next on null, on ended protocol, on moved value, on state HasNext (got: HasNext, Next))
    return iterator.next();
  }

  public static void main() {
    WrapperWithoutProtocol1 wrapper = new WrapperWithoutProtocol1(new JavaIterator());
    // :: error: (Cannot call hasNext on null, on ended protocol, on moved value)
    wrapper.iterator.hasNext();
  }

}
