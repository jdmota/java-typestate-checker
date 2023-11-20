import jatyc.lib.*;

@Typestate("RobotNodeProtocol")
public class RobotNode {
  private @Nullable RobotNode next;
  private @Nullable Robot element;

  public RobotNode(@Requires("IDLE") Robot r) {
    element = r;
    next = null;
  }

  public @Ensures("IDLE") Robot take() {
    Robot r = element;
    element = null;
    return r;
  }

  public void putBack(@Requires("IDLE") Robot r) {
    element = r;
  }

  public @Nullable @Ensures("INIT") RobotNode getNext() {
    RobotNode n = next;
    next = null;
    return n;
  }

  public void setLast(@Requires("INIT") RobotNode e) {
    if (next == null) next = e;
    else next.setLast(e);
  }
}
