import mungo.lib.Typestate;

@Typestate("Derived.protocol")
public class Derived extends Base {
  public boolean hasNext() {
    return false;
  }

  public void next() {

  }

  public void remove() {

  }
}
