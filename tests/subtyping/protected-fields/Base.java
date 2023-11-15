import jatyc.lib.Typestate;

@Typestate("Base.protocol")
// :: error: ([this.obj] did not complete its protocol (found: State{SomeObj, Init}))
public class Base {
  protected SomeObj obj;

  public Base() {
    // :: warning: (this.obj: Null)
    this.obj = new SomeObj();
  }

  public boolean hasNext() {
    return someBool();
  }

  public void next() {

  }

  private static boolean someBool() {
    return true;
  }
}
