public class Shared2 {
  // :: error: (Object did not complete its protocol. Type: State "Init" | Ended)
  private Linear l;

  public Shared2() {
    l = new Linear();
  }

  public synchronized void change() {
    // :: error: (Cannot call change on ended protocol)
    l.change();
  }
}
