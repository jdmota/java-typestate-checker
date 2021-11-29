public class Example3 {
  public static void main(String[] args) {
    BaseIterator it = new BaseIterator();
    it.init(args);
    while (!it.hasNext()) {
      System.out.println(it.next());
    }
    /*
    If we pass an empty array:
    Exception in thread "main" java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
    */
  }
}
