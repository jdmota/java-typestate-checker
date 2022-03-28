import java.util.List;

public class Example {
  static void iterate(List<Object> list) {
    BaseIterator it = new RemovableIterator(list);
    if (!it.hasNext()) {
      System.out.println(it.next());
    }
  }
}
