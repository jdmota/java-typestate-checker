import jatyc.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("Node")
public class Node {
  private @Nullable Object value;
  private @Nullable Node next;

  public Node() {
    // :: warning: (this.value: Null)
    this.value = null;
    // :: warning: (this.next: Null)
    this.next = null;
  }

  public void setValue(Object v) {
    // :: warning: (v: Shared{java.lang.Object})
    // :: warning: (this.value: Null)
    value = v;
  }

  public void setNext(Node n) {
    // :: warning: (n: Shared{Node})
    // :: warning: (this.next: Null)
    next = n;
  }

  public Object getValue() {
    // "value" is never null here because "setValue" is always called before
    // If the class analysis works, no error should be reported here
    // :: warning: (this.value: Shared{java.lang.Object})
    return value;
  }

  public Node getNext() {
    // "next" is never null here because "setNext" is always called before
    // If the class analysis works, no error should be reported here
    // :: warning: (this.next: Shared{Node})
    return next;
  }
}
