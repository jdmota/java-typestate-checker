import org.checkerframework.checker.mungo.lib.MungoTypestate;
import org.checkerframework.checker.mungo.lib.MungoState;
import org.checkerframework.checker.mungo.lib.MungoNullable;

import java.util.Iterator;

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    iterator = it;
  }

  public boolean hasNext() {
    return iterator.hasNext();
  }

  public Object next() {
    return iterator.next();
  }

}
