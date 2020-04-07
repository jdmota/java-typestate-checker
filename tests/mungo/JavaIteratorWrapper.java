import org.checkerframework.checker.mungo.lib.MungoTypestate;
import org.checkerframework.checker.mungo.lib.MungoState;
import org.checkerframework.checker.mungo.lib.MungoNullable;

import java.util.Iterator;

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper1 {

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

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper2 {

  private @MungoNullable JavaIterator iterator = null;

  // :: error: (Object did not complete its protocol)
  public void init(JavaIterator it) {

  }

  public boolean hasNext() {
    // :: error: (Cannot call hasNext on null)
    return iterator.hasNext();
  }

  public Object next() {
    return iterator.next();
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper3 {

  // :: error: (Object did not complete its protocol)
  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    iterator = it;
  }

  public boolean hasNext() {
    return true;
  }

  public Object next() {
    // :: error: (Cannot call next on state HasNext (got: HasNext, Next))
    return iterator.next();
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper4 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    iterator = it;
  }

  public boolean hasNext() {
    // :: error: (Cannot call hasNext on ended protocol)
    while (iterator.hasNext()) {
      iterator.next();
    }
    return false; // TODO detect that this always returns false and "next" will never be called?
  }

  public Object next() {
    // :: error: (Cannot call next on ended protocol)
    return iterator.next();
  }

}
