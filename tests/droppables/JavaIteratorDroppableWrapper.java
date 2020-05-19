import org.checkerframework.checker.mungo.lib.MungoTypestate;
import org.checkerframework.checker.mungo.lib.MungoRequires;
import org.checkerframework.checker.mungo.lib.MungoNullable;

import java.util.function.Supplier;

@MungoTypestate("JavaIteratorDroppableWrapper.protocol")
class JavaIteratorDroppableWrapper1 {

  private JavaIteratorDroppable iterator = new JavaIteratorDroppable();

  public boolean hasNext() {
    // :: warning: (iterator: JavaIteratorDroppable{HasNext|Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: JavaIteratorDroppable{Next})
    return iterator.next();
  }

}

@MungoTypestate("JavaIteratorDroppableWrapper.protocol")
class JavaIteratorDroppableWrapper2 {

  // :: error: (Object did not complete its protocol. Type: JavaIterator{HasNext})
  // :: error: (Object did not complete its protocol. Type: JavaIterator{Next})
  private JavaIterator iterator = new JavaIterator();

  public boolean hasNext() {
    // :: warning: (iterator: JavaIterator{HasNext|Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: JavaIterator{Next})
    return iterator.next();
  }

}
