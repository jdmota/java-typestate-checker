import jatyc.lib.*;

@Typestate("QueueNodeProtocol")
public class QueueNode {
  private @Nullable QueueNode next;
  private Robot element;

  public QueueNode(@Requires("IDLE") Robot r) {
    element = r;
    next = null;
  }

  public @Nullable @Ensures("INIT") QueueNode getNext() {return next;}

  public void setLast(@Requires("INIT") QueueNode e) {
    if(next == null) next = e;
    else next.setLast(e);
  }
  public @Ensures("IDLE") Robot getElement() {return element;}

}
