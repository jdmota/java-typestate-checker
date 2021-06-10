import mungo.lib.Typestate;

@Typestate("Derived.protocol")
// :: error: ([this.obj] did not complete its protocol (found: Unknown))
public class Derived extends Base {
  public void remove() {
    // :: warning: (this.obj: Bottom)
    this.obj.close();
  }
}
