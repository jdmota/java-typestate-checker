import jatyc.lib.Requires;
import base.BaseIterator;

public class Example2 {
  public static void main(String[] args) {
    BaseIterator it = new RemovableIterator(args);
    RemovableIterator remIt = (RemovableIterator) iterate(it);
    System.out.printf("Left: %d\n", remIt.remainingItems());
  }

  public static BaseIterator iterate(@Requires("HasNext") BaseIterator it) {
    while (it.hasNext()) {
      System.out.printf("Item: %s\n", it.next());
    }
    return it;
  }
}
