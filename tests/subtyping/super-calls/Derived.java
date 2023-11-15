import jatyc.lib.Typestate;

@Typestate("Derived.protocol")
public class Derived extends Base {
  private ObjectWithProtocol obj;

  public Derived() {
    super();
    // :: warning: (this.obj: Null)
    this.obj = new ObjectWithProtocol();
    // :: warning: (this.obj: State{ObjectWithProtocol, INIT})
    this.obj.close();
  }

  public boolean hasNext() {
    // :: error: (Cannot call own public method [hasNext])
    return super.hasNext();
  }

  public void remove() {

  }
}
