public class Example2 {
  public static void main(String[] args) {
    BaseIterator it = new CircularIterator(args);    
    do {
      // Down-cast
      CircularIterator circularIt = (CircularIterator) it;
      if (circularIt.hasNext()) {
        System.out.println(circularIt.next());
        circularIt.remove();
        // Up-cast
        it = circularIt;
      } else break;
    } while (true);
  }
}
