import org.checkerframework.checker.mungo.lib.MungoTypestate;
import org.checkerframework.checker.mungo.lib.MungoState;
import org.checkerframework.checker.mungo.lib.MungoNullable;

import java.util.function.Supplier;

@MungoTypestate("JavaIteratorDroppable.protocol")
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
