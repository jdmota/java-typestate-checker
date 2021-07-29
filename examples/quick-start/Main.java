public class Main {
  public static void main(String[] args) { // error: [iterator] did not complete its protocol
    JavaIterator iterator = new JavaIterator();

    while (!iterator.hasNext()) {
      iterator.next(); // error: Cannot call [next] on State{JavaIterator, end}
    }
  }
}
