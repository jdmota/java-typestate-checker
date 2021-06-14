import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Nullable;

@Typestate("JavaIteratorDroppable2.protocol")
public class JavaIteratorDroppable2 {

  public boolean hasNext() {
    return false;
  }

  public String next() {
    return "";
  }

  public static void main() {
    JavaIteratorDroppable2 it = new JavaIteratorDroppable2();
    // :: warning: (it: State{JavaIteratorDroppable2, HasNext})
    it.hasNext();
  }

}
