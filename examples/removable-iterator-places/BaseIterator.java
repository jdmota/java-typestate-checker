import java.util.List;
import jatyc.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("BaseIterator")
public class BaseIterator {
  protected List<Object> items;
  protected int index;

  public BaseIterator(List<Object> items) {
    this.items = items;
    this.index = 0;
  }
  public boolean hasNext() { return this.index < this.items.size(); }
  public @Nullable Object next() { return this.items.get(this.index++); }
  public int remainingItems() { return this.items.size() - this.index; }
}
