import java.util.*;
import java.util.function.Supplier;

public class NotOk {
  public static void main1(String[] args) {
    JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
  }

  public static void main2(String[] args) {
    JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
    use(it);
  }

  public static void main3(String[] args) {
    JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
    Supplier<Boolean> fn = () -> {
      return it.hasNext();
    };
  }

  public static void use(JavaIterator it) {

  }
}
