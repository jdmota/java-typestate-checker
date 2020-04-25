import java.util.*;

public class Ok {
  public static void main1(String[] args) {
    JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
    use(it);
  }

  public static void main2(String[] args) {
    JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
    JavaIterator it2 = it;
    use(it2);
  }

  public static void use(JavaIterator it) {
    while (it.hasNext() == Boolean.True) {
      System.out.println(it.next());
    }
  }
}
