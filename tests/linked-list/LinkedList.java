import org.checkerframework.checker.mungo.lib.MungoTypestate;
import org.checkerframework.checker.mungo.lib.MungoNullable;

public class LinkedList {

  private static class Node {

    // :: error: (Object did not complete its protocol. Type: Item{State0|State1} | Ended | Null | Moved)
    public @MungoNullable Item value = null;
    public @MungoNullable Node next;

    private Node(Item value) {
      // :: warning: (value: Item{State0|State1})
      this.value = value;
      this.next = null;
    }

  }

  private @MungoNullable Node head;
  private @MungoNullable Node tail;

  public LinkedList() {
    this.head = null;
    this.tail = null;
  }

  public void add(Item value) {
    // :: warning: (value: Item{State0|State1})
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

  public @MungoNullable Item get(int idx) {
    @MungoNullable Node node = this.head;
    // :: warning: (node: NoProtocol | Null)
    for (int i = 0; node != null && i < idx; i++) {
      node = node.next;
    }
    // type of expression: Item{State0|State1} | Null | Ended | Moved
    // method return type: Item{State0|State1} | Null
    // :: warning: (node: NoProtocol | Null)
    // :: error: (return.type.incompatible)
    return node == null ? null : node.value;
  }

}
