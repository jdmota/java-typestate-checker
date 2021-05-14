import org.checkerframework.checker.jtc.lib.Typestate;
import org.checkerframework.checker.jtc.lib.Nullable;

public class LinkedList {

  private static class Node {

    // :: error: (Object did not complete its protocol. Type: Unknown)
    public @Nullable Item value = null;
    public @Nullable Node next;

    private Node(Item value) {
      // :: warning: (value: State "State0" | State "State1")
      this.value = value;
      this.next = null;
    }

  }

  private @Nullable Node head;
  private @Nullable Node tail;

  public LinkedList() {
    this.head = null;
    this.tail = null;
  }

  public void add(Item value) {
    // :: warning: (value: State "State0" | State "State1")
    Node n = new Node(value);
    // :: warning: (tail: NoProtocol | Null)
    if (tail == null) {
      // :: warning: (head: NoProtocol | Null)
      head = n;
      // :: warning: (tail: Null)
      tail = n;
    } else {
      tail.next = n;
      tail = n;
    }
  }

  public @Nullable Item get(int idx) {
    @Nullable Node node = this.head;
    // :: warning: (node: NoProtocol | Null)
    for (int i = 0; node != null && i < idx; i++) {
      node = node.next;
    }
    // type of expression: State "State0" | State "State1" | Null | Ended | Moved
    // method return type: State "State0" | State "State1" | Null
    // :: warning: (node: NoProtocol | Null)
    // :: error: (return.type.incompatible)
    // :: error: (Access of object with protocol inside object without protocol might break linearity)
    return node == null ? null : node.value;
  }

}
