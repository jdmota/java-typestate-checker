import java.util.Iterator;
import mungo.lib.Typestate;
import mungo.lib.Boolean;

@Typestate("JavaIteratorProtocol")
public class JavaIterator {

  private Iterator<String> it;

  public JavaIterator(Iterator<String> it) {
    this.it = it;
  }

	public Boolean hasNext() {
    return it.hasNext() ? Boolean.True : Boolean.False;
  }

  public String next() {
    return it.next();
  }

}
