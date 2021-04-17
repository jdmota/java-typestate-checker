import mungo.lib.Typestate;

@Typestate("Derived.protocol")
public class Derived extends Base {
  public void remove() {
    // :: error: (Cannot call close on unknown)
    // :: error: (Returned object did not complete its protocol. Type: Unknown)
    this.obj.close();
  }
}
