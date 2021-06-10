import org.checkerframework.checker.jtc.lib.Typestate;
import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.Nullable;

@Typestate("LinkedList")
public class LinkedList {

  private @Nullable Node head;
  private @Nullable Node tail;

  public LinkedList() {
    // :: warning: (this.head: Null)
    this.head = null;
    // :: warning: (this.tail: Null)
    this.tail = null;
  }

  public void add(@Requires("State0") Item value) {
    // :: warning: (value: State{Item, State0})
    Node n = new Node(value);
    // :: warning: (this.tail: Shared{Node} | Null)
    if (tail == null) {
      // :: warning: (this.head: Shared{Node} | State{Node, State0} | Null)
      // :: warning: (n: State{Node, State0})
      // :: error: (The previous value of [this.head] did not complete its protocol (found: Shared{Node} | State{Node, State0} | Null))
      head = n;
      // :: warning: (this.tail: Null)
      // :: warning: (n: Shared{Node})
      tail = n;
    } else {
      // :: warning: (this.tail: Shared{Node})
      // :: warning: (n: State{Node, State0})
      // :: error: (Cannot call [setNext] on Shared{Node})
      tail.setNext(n);
      // :: warning: (n: Shared{Node})
      // :: warning: (this.tail: Bottom)
      tail = n;
    }
  }

  // :: error: ([node] did not complete its protocol (found: State{Node, State0} | Null))
  public @Nullable Item get(int idx) {
    // :: warning: (this.head: Shared{Node} | State{Node, State0} | Null)
    @Nullable Node node = this.head;
    // :: warning: (node: Shared{Node} | State{Node, State0} | Null)
    for (int i = 0; node != null && i < idx; i++) {
      // :: warning: (node: Shared{Node} | State{Node, State0} | Null)
      // :: error: (Cannot call [getNext] on State{Node, State0})
      // :: error: (Cannot call [getNext] on Shared{Node} | State{Node, State0})
      // :: error: (Cannot call getNext on null)
      node = node.getNext();
    }
    // :: warning: (node: Shared{Node} | State{Node, State0} | Null)
    // :: warning: (node: Shared{Node} | State{Node, State0})
    // :: error: (Cannot call [getValue] on Shared{Node} | State{Node, State0})
    return node == null ? null : node.getValue();
  }

}
