import mungo.lib.Typestate;

@Typestate("Derived")
public class Derived implements Base {

  public boolean hasNext() {
    return false;
  }

  public void next() {

  }

  public void remove() {

  }
}
