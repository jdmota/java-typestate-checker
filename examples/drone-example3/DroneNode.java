import jatyc.lib.*;

@Typestate("DroneNodeProtocol")
public class DroneNode {
  private @Nullable DroneNode next;
  private @Nullable PendingDrone element;

  public DroneNode(@Requires({"NO_TASK_HOVERING", "WITH_TASK_FLYING"}) PendingDrone p) {
    element = p;
    next = null;
  }

  public @Ensures({"NO_TASK_HOVERING", "WITH_TASK_FLYING"}) PendingDrone take() {
    PendingDrone p = element;
    element = null;
    return p;
  }

  public void putBack(@Requires({"NO_TASK_HOVERING", "WITH_TASK_FLYING"}) PendingDrone p) {
    element = p;
  }

  public @Nullable @Ensures("INIT") DroneNode getNext() {
    DroneNode n = next;
    next = null;
    return n;
  }

  public void setLast(@Requires("INIT") DroneNode n) {
    if (next == null) next = n;
    else next.setLast(n);
  }
}
