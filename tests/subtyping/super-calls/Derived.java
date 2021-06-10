import mungo.lib.Typestate;

@Typestate("Derived.protocol")
public class Derived extends Base {
  public boolean hasNext() {
    // :: error: (Cannot call own public method [hasNext])
    return super.hasNext();
  }

  public void remove() {

  }
}
