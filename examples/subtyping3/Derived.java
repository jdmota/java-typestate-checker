import mungo.lib.Typestate;

@Typestate("Derived")
public class Derived extends Base {
  public boolean hasNext() {
    return true;
  }

  public void next() {

  }

  public void remove() {

  }
}
