public class ClientCode {
  public static void main(String[] args) {
    Wrapper w = new Wrapper();
    w.init(new JavaIterator());
    while (w.hasNext()) {
      w.next();
    }
  }
}
