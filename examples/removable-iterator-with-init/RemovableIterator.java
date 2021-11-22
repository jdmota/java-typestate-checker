import java.util.*;
import jatyc.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("RemovableIterator")
public class RemovableIterator extends BaseIterator {
  protected @Nullable List<Object> items;

  public RemovableIterator() {
    super();
    this.items = null;
  }

  public void init(String[] items) {
    this.items = Util.toList(items);
  }

  public boolean hasNext() {
    return this.index < this.items.size();
    }

  public @Nullable Object next() {
    return this.items.get(this.index++);
  }

  public void remove() {
    this.items.remove(--this.index);
  }
}
