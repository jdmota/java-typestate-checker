import jatyc.lib.*;
import java.util.*;

public class ClientCode {

  public static void main(String[] args) {
    DroneGroup group = flyingDroneGroup(4);
    List<DroneTask> taskList = initTask(
      new DroneTask(10.4034, 11.4392, "pic"),
      new DroneTask(10.4034, 64.4392, "video"),
      new DroneTask(11.4034, 0.4392, "xRayPic"),
      new DroneTask(11.4034, 0.4392, "pic"),
      new DroneTask(11.4034, 0.4392, "xRayPic"),
      new DroneTask(-6.4034, 1.4392, "video")
    );

    while (!taskList.isEmpty()) {
      PendingDrone p = group.take();
      if (p.completed()) {
        Drone d = p.takeHoveringDrone();
        DroneTask task = taskList.get(0);
        if (task == null) throw new RuntimeException();

        switch (task.getTask()) {
          case "pic":
            d.setDestination(task.getX(), task.getY());
            p.setTask(d, task);
            taskList.remove(0);
            break;
          case "video":
            if (d instanceof XRayDrone) {
              d.setDestination(task.getX(), task.getY());
              ((XRayDrone) d).recordVideo();
              p.setTask(d, task);
              taskList.remove(0);
            } else {
              p.finishTask(d);
            }
            break;
          case "xRayPic":
            if (d instanceof XRayDrone) {
              d.setDestination(task.getX(), task.getY());
              p.setTask(d, task);
              taskList.remove(0);
            } else {
              p.finishTask(d);
            }
            break;
          default:
            throw new RuntimeException();
        }
      } else {
        Drone d = p.takeFlyingDrone();

        if (d.hasArrived()) {
          if (d instanceof XRayDrone) {
            switch (p.getTask().getTask()) {
              case "pic":
                d.takePicture();
                break;
              case "video":
                break;
              case "xRayPic":
                ((XRayDrone) d).xRayPicture();
                break;
            }
          } else {
            d.takePicture();
          }
          p.finishTask(d);
        } else {
          p.continueTask(d);
        }  
      }
      group.putBack(p);
      group.next();
    }

    group.landAll();
    System.out.println("Done!");
  }

  private static @Ensures("NON_EMPTY") DroneGroup flyingDroneGroup(int n_drone) {
    if (n_drone <= 0) System.out.println("n_drone must be > 0, creating 1 anyway");
    DroneGroup group = new DroneGroup();
    do {
      Drone d = null;
      if (n_drone % 2 == 0) d = new Drone();
      else d = new XRayDrone();
      n_drone--;
      d.takeOff();
      PendingDrone p = new PendingDrone(d);
      group.add(p);
    } while (n_drone > 0);
    return group;
  }

  private static List<DroneTask> initTask(DroneTask... tasks) {
    List<DroneTask> taskList = new ArrayList<>();
    for (DroneTask task : taskList) taskList.add(task);
    return taskList;
  }

  private static void sleep(int millisec) {
    try { Thread.sleep(millisec); }
    catch (InterruptedException e ) {}
  }
}
