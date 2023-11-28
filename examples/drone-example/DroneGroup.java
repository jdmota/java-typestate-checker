import jatyc.lib.*;

@Typestate("DroneGroupProtocol")
public class DroneGroup {
  private @Nullable DroneNode fst;

  public DroneGroup() {
    fst = null;
  }

  public void add(@Requires("HOVERING") Drone d) {
    DroneNode n = new DroneNode(d);
    if (fst == null) fst = n;
    else fst.setLast(n);
  }

  public @Ensures("HOVERING") Drone take() {
    return fst.take();
  }

  public void putBack(@Requires("HOVERING") Drone d) {
    fst.putBack(d);
  }

  public void next() {
    DroneNode n = fst;
    fst = n.getNext();

    if (fst == null) fst = n;
    else fst.setLast(n);
  }

  public void landAll() {
    while (fst != null) {
      Drone drone = fst.take();
      drone.land();
      drone.shutDown();
      fst = fst.getNext();
    }
  }
}
