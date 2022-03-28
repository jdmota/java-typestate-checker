import java.util.List;
import jatyc.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("RemovableIterator")
public class RemovableIterator extends BaseIterator {
  public RemovableIterator(List<Object> items) {
    super(items);
  }
  public void remove() {
    this.items.remove(--this.index);
  }
}
