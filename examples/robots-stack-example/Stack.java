import jatyc.lib.*;


@Typestate("StackProtocol")
public class Stack {

  private @Nullable StackNode top;
  public Stack() {
    top = null;
  }

  public void push(@Requires("IDLE") Robot r) {
    top = new StackNode(r, top);
  }

  public @Ensures("IDLE") Robot pop() {
    Robot robot = top.getElement();
    top = top.getPrevious();
    return robot;
  }

  public boolean isEmpty() {return top == null;}
}
