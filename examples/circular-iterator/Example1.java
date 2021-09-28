public class Example1 {
  public static void main(String[] args) {
    CircularIterator it = new CircularIterator(args);
    while (it.hasNext()) {
      String item = it.next();
      it.remove();
      System.out.printf("Item: %s, Items left: %d\n", item, it.countItems());
    }
  }
}
