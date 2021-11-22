import jatyc.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("BaseIterator")
public class BaseIterator {
  private String @Nullable [] items;
  protected int index;

  public BaseIterator() {
    this.items = null;
    this.index = 0;
  }

  public void init(String[] items) {
    this.items = items;
  }

  public boolean hasNext() {
    return this.index < this.items.length;
  }

  public @Nullable Object next() {
    return this.items[this.index++];
  }
}
