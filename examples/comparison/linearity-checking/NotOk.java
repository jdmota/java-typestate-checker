import java.util.*;

public class NotOk {
  public static void main1(String[] args) {
    JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
    use(it);
    it.hasNext();
  }

  public static void main2(String[] args) {
    JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
    use(it);
    use(it);
  }

  public static void main3(String[] args) {
    JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
    JavaIterator it2 = it;
    use(it2);
    it.hasNext();
  }

  public static void main4(String[] args) {
    JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
    JavaIterator it2 = it;
    use(it2);
    use(it);
  }

  public static void use(JavaIterator it) {
    while (it.hasNext() == Boolean.True) {
      System.out.println(it.next());
    }
  }
}
