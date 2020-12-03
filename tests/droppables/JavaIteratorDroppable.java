import org.checkerframework.checker.jtc.lib.Typestate;
import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIteratorDroppable.protocol")
public class JavaIteratorDroppable {

  public boolean hasNext() {
    return false;
  }

  public String next() {
    return "";
  }

  public static void main() {
    JavaIteratorDroppable it = new JavaIteratorDroppable();
  }

}
