public class Shared {
  // :: error: (Object did not complete its protocol. Type: State "Init" | Ended)
  private Linear l;

  public Shared() {
    l = new Linear();
  }

  public void change() {
    // :: error: (Cannot call change on ended protocol)
    // :: error: (Access of object with protocol inside object without protocol might break linearity)
    l.change();
  }
}
