import jatyc.lib.*;

@Typestate("DroneGroupProtocol")
public class DroneGroup {
  private @Nullable DroneNode fst;

  public DroneGroup() {
    fst = null;
  }

  public void add(@Requires({"NO_TASK_HOVERING", "WITH_TASK_FLYING"}) PendingDrone p) {
    DroneNode n = new DroneNode(p);
    if (fst == null) fst = n;
    else fst.setLast(n);
  }

  public @Ensures({"NO_TASK_HOVERING", "WITH_TASK_FLYING"}) PendingDrone take() {
    return fst.take();
  }

  public void putBack(@Requires({"NO_TASK_HOVERING", "WITH_TASK_FLYING"}) PendingDrone p) {
    fst.putBack(p);
  }

  public void next() {
    DroneNode n = fst;
    fst = n.getNext();

    if (fst == null) fst = n;
    else fst.setLast(n);
  }

  public void landAll() {
    while (fst != null) {
      PendingDrone p = fst.take();
      Drone drone;
      if (p.completed()) {
        drone = p.takeHoveringDrone();
      } else {
        drone = p.takeFlyingDrone();
        while (!drone.hasArrived()) {}
      }
      drone.land();
      drone.shutDown();
      fst = fst.getNext();
    }
  }
}
