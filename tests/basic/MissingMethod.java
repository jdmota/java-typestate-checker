import jatyc.lib.Typestate;

@Typestate("JavaIterator.protocol")
public class MissingMethod {

  public boolean hasNext() {
    return false;
  }

  public String next() {
    return "";
  }

  // :: error: (Method [unusedMethod] does not appear in the typestate)
  public void unusedMethod() {

  }

}
