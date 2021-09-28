import jatyc.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("BaseIterator")
public class BaseIterator {
  protected String[] items;
  protected int index;

  public BaseIterator(String[] items) {
    this.items = items;
    this.index = 0;
  }
  public boolean hasNext() {
    return this.index < this.items.length;
  }
  public @Nullable String next() {
    return this.items[this.index++];
  }
  public int countItems() {
    return this.items.length - this.index;
  }
}
