import jatyc.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("RemovableIterator")
public class RemovableIterator extends BaseIterator {
  private @Nullable Next previous;

  public RemovableIterator(LinkedList head) { super(head); }

  public boolean hasNext() {
    this.previous = this.current;
    this.current = this.current.getNext();
    return this.current != null;
  }

  public void remove() {
    this.previous.setNext(this.current.getNext());
    this.current = previous;
  }
}
