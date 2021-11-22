public class Example2 {
  public static void main(String[] args) {
    BaseIterator it = new RemovableIterator(args);
    do {
      // Down-cast
      RemovableIterator remIt = (RemovableIterator) it;
      if (remIt.hasNext()) {
        System.out.printf("Item: %s\n", remIt.next());
        remIt.remove();
        // Up-cast
        it = remIt;
      } else break;
    } while (true);
  }
}
