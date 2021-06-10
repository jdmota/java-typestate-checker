import mungo.lib.Typestate;

public class Derived extends Base {
  // :: error: (Method [remove] does not appear in the typestate)
  public void remove() {

  }
}
