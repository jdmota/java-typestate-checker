import mungo.lib.Typestate;

@Typestate("Derived.protocol")
public class Derived extends Base {
  public boolean hasNext() {
    // :: error: (Cannot call its own public method)
    return super.hasNext();
  }

  public void remove() {

  }
}
