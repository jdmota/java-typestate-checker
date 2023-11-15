import jatyc.lib.*;

@Typestate("Stack")
public class Stack {
  private @Nullable StackNode top;

  public Stack() {
    // :: warning: (this.top: Null)
    top = null;
  }

  public void push(@Requires("DISC") Socket s) {
    // :: warning: (s: State{Socket, DISC})
    // :: warning: (this.top: Null)
    // :: warning: (this.top: State{StackNode, INIT})
    // :: warning: (this.top: State{StackNode, INIT} | Null)
    // :: warning: (this.top: Shared{StackNode})
    // :: warning: (this.top: Shared{StackNode} | Null)
    top = new StackNode(s, top);
  }

  public @Ensures("DISC") Socket pop() {
    // :: warning: (this.top: State{StackNode, INIT})
    Socket s = top.getElement();
    // :: warning: (this.top: State{StackNode, NO_ELEM})
    // :: warning: (this.top: State{StackNode, end})
    top = top.getPrevious();
    // :: warning: (s: State{Socket, DISC})
    return s;
  }

  public boolean isEmpty() {
    // :: warning: (this.top: Null)
    // :: warning: (this.top: State{StackNode, INIT})
    // :: warning: (this.top: State{StackNode, INIT} | Null)
    return top == null;
  }
}
