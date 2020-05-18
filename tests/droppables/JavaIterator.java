import org.checkerframework.checker.mungo.lib.MungoTypestate;
import org.checkerframework.checker.mungo.lib.MungoState;
import org.checkerframework.checker.mungo.lib.MungoNullable;

import java.util.function.Supplier;

@MungoTypestate("JavaIterator.protocol")
public class JavaIterator {

  public boolean hasNext() {
    return false;
  }

  public String next() {
    return "";
  }

  public static void main() {
    // :: error: (Object did not complete its protocol. Type: JavaIterator{HasNext})
    JavaIterator it = new JavaIterator();
  }

}
