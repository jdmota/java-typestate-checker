public class Example1 {
  public static void main(String[] args) {
    LinkedList l = new LinkedList(new Element("a", new Element("b", new Element("c", new Element("d",null)))));
    System.out.println("Full list: " + l.toString());
    RemovableIterator it = new RemovableIterator(l);
    while (it.hasNext()) {
      String item = it.next();
      System.out.println("Remaining list: " + l.toString());
      System.out.printf("Removed: %s, Items left: %d\n", item, it.countItems());
      c++;
    }
  }
}
