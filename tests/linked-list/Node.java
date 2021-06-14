import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Nullable;

@Typestate("Node")
public final class Node {

  private Item value;
  private @Nullable Node next;

  public Node(@Requires("State0") Item value) {
    // :: warning: (this.value: Null)
    // :: warning: (value: State{Item, State0})
    this.value = value;
    // :: warning: (this.next: Null)
    this.next = null;
  }

  public Item getValue() {
    // :: warning: (this.value: State{Item, State0})
    return value;
  }

  public @Nullable Node getNext() {
    // :: warning: (this.next: State{Node, State0} | Null)
    return next;
  }

  public void setNext(@Requires("State0") Node next) {
    // :: warning: (next: State{Node, State0})
    // :: warning: (this.next: Null)
    this.next = next;
  }

}
