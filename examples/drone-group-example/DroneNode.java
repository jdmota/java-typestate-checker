import jatyc.lib.*;

@Typestate("DroneNodeProtocol")
public class DroneNode {
  private @Nullable DroneNode next;
  private @Nullable Drone element;

  public DroneNode(@Requires("HOVERING") Drone r) {
    element = r;
    next = null;
  }

  public @Ensures("HOVERING") Drone take() {
    Drone r = element;
    element = null;
    return r;
  }

  public void putBack(@Requires("HOVERING") Drone r) {
    element = r;
  }

  public @Nullable @Ensures("INIT") DroneNode getNext() {
    DroneNode n = next;
    next = null;
    return n;
  }

  public void setLast(@Requires("INIT") DroneNode e) {
    if (next == null) next = e;
    else next.setLast(e);
  }
}
