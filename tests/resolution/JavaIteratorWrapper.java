import org.checkerframework.checker.jtc.lib.Typestate;
import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.Nullable;

import java.util.function.Supplier;

import utils.JavaIterator;

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper1 {

  private @Nullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: State "HasNext" | State "Next")
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (iterator: State "HasNext" | State "Next")
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: State "Next")
    return iterator.next();
  }

}
