import jatyc.lib.*;

@Typestate("StackNodeProtocol")
public class StackNode {
  private @Nullable StackNode previous;
  private Robot element;

  public StackNode(@Requires("IDLE") Robot r, @Nullable @Requires("INIT") StackNode p) {
    element = r;
    previous = p;
  }

  public @Nullable @Ensures("INIT") StackNode getPrevious() {return previous;}

  public @Ensures("IDLE") Robot getElement() {return element;}

}
