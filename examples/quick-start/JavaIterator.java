import jatyc.lib.Typestate;

@Typestate("JavaIterator")
public class JavaIterator {
  public boolean hasNext() {
    return false;
  }

  public Object next() {
    return new Object();
  }
}
