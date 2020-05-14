import org.checkerframework.checker.mungo.lib.MungoTypestate;
import org.checkerframework.checker.mungo.lib.MungoState;
import org.checkerframework.checker.mungo.lib.MungoNullable;

import java.util.function.Supplier;

import utils.JavaIterator;

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper1 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Ended | Moved | Null)
    // :: warning: (it: JavaIterator{HasNext|Next})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (iterator: JavaIterator{HasNext|Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: JavaIterator{Next})
    return iterator.next();
  }

}
