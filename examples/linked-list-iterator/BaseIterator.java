import jatyc.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("BaseIterator")
public class BaseIterator {
  protected Next current;

  public BaseIterator(LinkedList head) { this.current = head; }
  public boolean hasNext() {
    this.current = this.current.getNext();
    return this.current != null;
  }
  public String next() {
    Element e = (Element) this.current;
    return e.getValue();
  }
  public int countItems() {
    return 0; // TODO
  }
}
