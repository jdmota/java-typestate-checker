import jatyc.lib.*;

@Typestate("DroneNodeProtocol")
public class DroneNode {
  private @Nullable DroneNode next;
  private @Nullable Drone element;

  public DroneNode(@Requires("HOVERING") Drone d) {
    element = d;
    next = null;
  }

  public @Ensures("HOVERING") Drone take() {
    Drone d = element;
    element = null;
    return d;
  }

  public void putBack(@Requires("HOVERING") Drone d) {
    element = d;
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
