import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Nullable;

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
