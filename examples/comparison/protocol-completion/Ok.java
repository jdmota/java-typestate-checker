import java.util.*;
import java.util.function.Supplier;

public class Ok {
  public static void main1(String[] args) {
    JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
    while (it.hasNext() == Boolean.True) {
      System.out.println(it.next());
    }
  }

  public static void main2(String[] args) {
    JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
    use(it);
  }

  public static void main3(String[] args) {
    Supplier<String> fn = () -> {
      JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
      use(it);
      return "";
    };
  }

  public static void use(JavaIterator it) {
    while (it.hasNext() == Boolean.True) {
      System.out.println(it.next());
    }
  }
}
