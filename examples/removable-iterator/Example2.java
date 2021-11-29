public class Example2 {
  public static void main(String[] args) {
    RemovableIterator it = new RemovableIterator(args);
    while (it.hasNext()) {
      System.out.println(it.next());
      it.remove();
    }
    BaseIterator baseIt = it; // Up-cast
    System.out.println(baseIt.remainingItems());
  }
}
