import mungo.lib.Typestate;

@Typestate("Derived.protocol")
// :: error: ([this.obj] did not complete its protocol (found: Shared{SomeObj} | State{SomeObj, ?}))
public class Derived extends Base {
  public void remove() {
    this.obj.close();
  }
}
