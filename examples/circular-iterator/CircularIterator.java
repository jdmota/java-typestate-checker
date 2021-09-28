import jatyc.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("CircularIterator")
public class CircularIterator extends BaseIterator {
  public CircularIterator(String[] items) {
    super(items);
  }
  public @Nullable String next() {
    String item = this.items[this.index++];
    if (this.items.length == this.index) this.index = 0;
    return item;
  }
  public void remove() {
    final int itemToRemove = this.index == 0 ? this.items.length - 1 : this.index - 1;
    String[] newItems = new String[this.items.length - 1];
    int counter = 0;
    for (int i = 0; i < this.items.length; i++) {
      if (i != itemToRemove) newItems[counter++] = this.items[i];
    }
    this.items = newItems;
    this.index = itemToRemove;
  }
}
