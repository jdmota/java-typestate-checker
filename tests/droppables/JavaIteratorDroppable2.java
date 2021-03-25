import org.checkerframework.checker.jtc.lib.Typestate;
import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.Nullable;

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
    // :: warning: (it: State "HasNext")
    it.hasNext();
  }

}
