package base;

import jatyc.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("../protocols/BaseIterator")
public class BaseIterator {
  private String[] items;
  protected int index;

  public BaseIterator(String[] items) {
    this.items = items;
    this.index = 0;
  }
  public boolean hasNext() {
    return this.index < this.items.length;
  }
  public @Nullable Object next() { return this.items[this.index++]; }
  public int remainingItems() { return this.items.length - this.index; }
}
