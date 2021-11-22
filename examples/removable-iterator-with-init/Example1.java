public class Example1 {
  public static void main(String[] args) {
    RemovableIterator it = new RemovableIterator();
    it.init(args);
    while (it.hasNext()) {
      Object item = it.next();
      it.remove();
      System.out.printf("Item: %s\n", item);
    }
  }
}
