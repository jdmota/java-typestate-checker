import jatyc.lib.*;

public class ClientCode {
  public static void main(String[] args) {
    BaseIterator it = new RemovableIterator(args);
    String toFind = "find me";
    if (it.hasNext()) {
      find(it, toFind);
    } else {
      System.out.println("No items");
    }
    System.out.printf("Done!");
  }

  public static boolean find(@Requires("Next") BaseIterator it, String toFind) {
    while (true) {
      Object curr = it.next();
      System.out.printf("Item: %s\n", curr);

      if (curr != null && curr.equals(toFind)) {
        System.out.println("Found!");
        return true;
      }
    }
  }
}
