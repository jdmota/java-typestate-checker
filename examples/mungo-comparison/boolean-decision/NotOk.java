import java.util.*;

public class NotOk {
  public static void main(String args[]) {
    JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());

    while (!it.hasNext()) {
      System.out.println(it.next());
    }
  }
}
