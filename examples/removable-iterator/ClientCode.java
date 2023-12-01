import jatyc.lib.*;

public class ClientCode {
  public static void main(String[] args) {
    BaseIterator it = new RemovableIterator(args);
    if (it.hasNext()) {
      iterate(it);
    } else {
      System.out.println("No items");
    }
    System.out.printf("Done!");
  }

  public static void iterate(@Requires("Next") BaseIterator it) {
    do {
      System.out.printf("Item: %s\n", it.next());
    } while (it.hasNext());
  }
}
