public class Main {
  public static void main(String[] args) {
    JavaIterator iterator = new JavaIterator();

    // Error!
    while (!iterator.hasNext()) {
      iterator.next();
    }
  }
}
