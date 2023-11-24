import jatyc.lib.*;

@Typestate("PendingDroneProtocol")
public class PendingDrone {

  private @Nullable DroneTask task;
  private Drone drone;

  public PendingDrone(@Requires("HOVERING") Drone drone) {
    this.task = null;
    this.drone = drone;
  }

  public DroneTask getTask() {
    return this.task;
  }

  public void setTask(@Requires("FLYING") Drone drone, DroneTask task) {
    this.task = task;
    this.drone = drone;
  }

  public void finishTask(@Requires("HOVERING") Drone drone) {
    this.task = null;
    this.drone = drone;
  }

  public void continueTask(@Requires("FLYING") Drone drone) {
    this.drone = drone;
  }

  public boolean completed() {
    return this.task == null;
  }

  public @Ensures("HOVERING") Drone takeHoveringDrone() {
    return this.drone;
  }

  public @Ensures("FLYING") Drone takeFlyingDrone() {
    return this.drone;
  }

}