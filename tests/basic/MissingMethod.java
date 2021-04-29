import org.checkerframework.checker.jtc.lib.Typestate;

@Typestate("JavaIterator.protocol")
public class MissingMethod {

  public boolean hasNext() {
    return false;
  }

  public String next() {
    return "";
  }

  // :: warning: (Method unusedMethod does not appear in the typestate)
  public void unusedMethod() {

  }

}
