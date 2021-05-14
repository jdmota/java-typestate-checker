import mungo.lib.Typestate;

@Typestate("Base.protocol")
public class Base {
  // :: error: (Object did not complete its protocol. Type: Unknown)
  protected SomeObj obj;

  public Base() {
    this.obj = new SomeObj();
  }

  public boolean hasNext() {
    return false;
  }

  public void next() {

  }
}
