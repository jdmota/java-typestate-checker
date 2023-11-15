import jatyc.lib.*;

@Typestate("StackNode")
public class StackNode {
  private @Nullable StackNode previous;
  private Socket element;

  public StackNode(@Requires("DISC") Socket s, @Nullable @Requires("INIT") StackNode p) {
    // :: warning: (s: State{Socket, DISC})
    // :: warning: (this.element: Null)
    element = s;
    // :: warning: (p: State{StackNode, INIT} | Null)
    // :: warning: (this.previous: Null)
    previous = p;
  }

  public @Nullable @Ensures("INIT") StackNode getPrevious() {
    // :: warning: (this.previous: State{StackNode, INIT} | Null)
    return previous;
  }

  public @Ensures("DISC") Socket getElement() {
    // :: warning: (this.element: State{Socket, DISC})
    return element;
  }
}
