public class Example3 {
  public static void main(String[] args) {
    CircularIterator it = new CircularIterator(args);
    while (!it.hasNext()) {
      System.out.printf("Item: %s\n", it.next());
    }
    /*
    If we pass an empty array:
    Exception in thread "main" java.lang.ArrayIndexOutOfBoundsException: Array index out of range: 0
        at CircularIterator.next(CircularIterator.java:10)
        at Example3.main(Example3.java:5)
    */
  }
}
