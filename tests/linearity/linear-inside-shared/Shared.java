import mungo.lib.Typestate;

public class Shared {
  // :: error: (Object did not complete its protocol. Type: State "Init" | Ended)
  // :: error: (Object with protocol inside object without protocol might break linearity)
  private Linear l;

  public Shared() {
    l = new Linear();
  }

  public void change() {
    // :: error: (Cannot call change on ended protocol)
    l.change();
  }
}
