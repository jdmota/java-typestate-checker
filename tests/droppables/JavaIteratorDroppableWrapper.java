import org.checkerframework.checker.jtc.lib.Typestate;
import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIteratorDroppableWrapper.protocol")
class JavaIteratorDroppableWrapper1 {

  private JavaIteratorDroppable iterator = new JavaIteratorDroppable();

  public boolean hasNext() {
    // :: warning: (iterator: State "HasNext" | State "Next")
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: State "Next")
    return iterator.next();
  }

}

@Typestate("JavaIteratorDroppableWrapper.protocol")
class JavaIteratorDroppableWrapper2 {

  // :: error: (Object did not complete its protocol. Type: State "HasNext")
  // :: error: (Object did not complete its protocol. Type: State "Next")
  private JavaIterator iterator = new JavaIterator();

  public boolean hasNext() {
    // :: warning: (iterator: State "HasNext" | State "Next")
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: State "Next")
    return iterator.next();
  }

}
