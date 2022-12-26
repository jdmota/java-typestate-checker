// :: error: ([this.l] did not complete its protocol (found: Shared{Linear} | State{Linear, ?}))
public class Shared {
  private Linear l;

  public Shared() {
    l = new Linear();
  }

  public void change() {
    // :: error: (Cannot call [change] on Shared{Linear})
    l.change();
  }

  public void change2() {
    // :: error: (Cannot assign because [this.l] is not accessible here)
    l = new Linear();
  }
}
