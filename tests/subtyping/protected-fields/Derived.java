import jatyc.lib.Typestate;

@Typestate("Derived.protocol")
// :: error: ([this.obj] did not complete its protocol (found: Shared{SomeObj} | State{SomeObj, ?}))
public class Derived extends Base {
  public void remove() {
    // :: warning: (this.obj: Shared{SomeObj} | State{SomeObj, ?})
    // :: error: (Cannot call [close] on Shared{SomeObj} | State{SomeObj, ?})
    this.obj.close();
  }
}
