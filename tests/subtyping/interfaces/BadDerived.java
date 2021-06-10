import mungo.lib.Typestate;

@Typestate("BadDerived")
// :: error: ([hasNext] transition(s) in [HasNext] of Base.protocol are not included in [Remove] of BadDerived.protocol)
public class BadDerived implements Base {

  public boolean hasNext() {
    return false;
  }

  public void next() {

  }

  // :: error: (Method [remove] does not appear in the typestate)
  public void remove() {

  }
}
