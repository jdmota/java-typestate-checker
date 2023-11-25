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
      DroneTask task = taskList.remove(0);
      if (task != null) {
        Drone d = areaScan(group.take(), task);
        group.putBack(d);
        group.next();
      }
    }
    group.landAll();
    System.out.println("Done!");
  }

  private static @Ensures("HOVERING") Drone areaScan(@Requires("HOVERING") Drone d, DroneTask task) {
    d.setDestination(task.getX(), task.getY());
    if (d instanceof XRayDrone) {
      XRayDrone xr = (XRayDrone) d;
      if (task.getTask().equals("video")) xr.recordVideo();
      while (!xr.hasArrived()) sleep(5000);
      switch (task.getTask()) {
        case "pic":
          xr.takePicture();
          break;
        case "xRayPic":
          xr.xRayPicture();
          break;
      }
      d = xr;
    } else {
      while (!d.hasArrived()) sleep(5000);
      d.takePicture();
    }
    return d;
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
      group.add(d);
    } while (n_drone > 0);
    return group;
  }

  private static List<DroneTask> initTask(DroneTask... tasks) {
    List<DroneTask> taskList = new ArrayList<>();
    for (DroneTask task : tasks) taskList.add(task);
    return taskList;
  }

  private static void sleep(int millisec) {
    try { Thread.sleep(millisec); }
    catch (InterruptedException e ) {}
  }
}
