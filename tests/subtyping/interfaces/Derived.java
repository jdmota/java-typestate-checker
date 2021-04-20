import mungo.lib.Typestate;

@Typestate("Derived.protocol")
public class Derived implements Base {

  public boolean hasNext() {
    return false;
  }

  public void next() {
    
  }

  public void remove() {
    
  }
}
