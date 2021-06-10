import org.checkerframework.checker.jtc.lib.Typestate;
import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIterator.protocol")
public class JavaIterator {

  public boolean hasNext() {
    return false;
  }

  public String next() {
    return "";
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext}))
  public static void main() {
    JavaIterator it = new JavaIterator();
  }

}
