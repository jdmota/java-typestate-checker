import jatyc.lib.*;

@Typestate("PendingDroneProtocol")
public class PendingDrone {

  private @Nullable DroneTask task;
  private Drone drone;

  public PendingDrone(@Requires("HOVERING") Drone drone) {
    // :: warning: (this.task: Null)
    this.task = null;
    // :: warning: (drone: State{Drone, HOVERING})
    // :: warning: (this.drone: Null)
    this.drone = drone;
  }

  public void setTask(@Requires("FLYING") Drone drone, DroneTask task) {
    // :: warning: (task: Shared{DroneTask})
    // :: warning: (this.task: Null)
    // :: warning: (this.task: Shared{DroneTask})
    this.task = task;
    // :: warning: (drone: State{Drone, FLYING})
    // :: warning: (this.drone: Shared{Drone})
    this.drone = drone;
  }

  public void finishTask(@Requires("HOVERING") Drone drone) {
    // :: warning: (this.task: Shared{DroneTask})
    this.task = null;
    // :: warning: (drone: State{Drone, HOVERING})
    // :: warning: (this.drone: Shared{Drone})
    this.drone = drone;
  }

  public boolean completed() {
    // :: warning: (this.task: Null)
    // :: warning: (this.task: Shared{DroneTask})
    return this.task == null;
  }

  public @Ensures("HOVERING") Drone takeHoveringDrone() {
    // :: warning: (this.drone: State{Drone, HOVERING})
    return this.drone;
  }

  public @Ensures("FLYING") Drone takeFlyingDrone() {
    // :: warning: (this.drone: State{Drone, FLYING})
    return this.drone;
  }

}
