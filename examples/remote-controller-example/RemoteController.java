import jatyc.lib.*;
import java.util.*;

class RemoteController {
  public static void useMultipleRobot(@Requires("NON_EMPTY") RobotGroup queue) {
    List<String> tasks = initTasks("weld", "move", "weld", "weld", "move");
    while (!tasks.isEmpty()) {
      String curr_task = tasks.remove(0);
      if (curr_task != null) {
        Robot r = attemptTask(queue.take(), curr_task);
        if (!r.taskResult()) tasks.add(curr_task);
        queue.putBack(r);
        queue.rotate();
      }
    }
    queue.turnAllOff();
  }

  public static void upcastFails() {
    List<String> tasks = initTasks("weld", "cut", "bend", "weld", "bend");
    MultiTaskRobot r1 = new MultiTaskRobot(new CutterArm());
    r1.turnOn();
    while (tasks.size() > 0) {
      String curr_task = tasks.remove(0);
      if (curr_task != null) {
        r1.executeTask(curr_task);
        if (!r1.taskResult()) {
          r1 = switchArm(r1, curr_task);
          tasks.add(0, curr_task);
        }
      }
    }
    r1.unplugArm();
    RobotGroup queue = poweredRobotRobotGroup(4);
    queue.add(r1); // upcast fails
    useMultipleRobot(queue);
  }

  private static @Ensures("IDLE") Robot attemptTask(@Requires("IDLE") Robot r, String task) {
    r.executeTask(task);
    if (!r.taskResult() && r instanceof MultiTaskRobot) {
      r = switchArm((MultiTaskRobot) r, task);
      r.executeTask(task);
    }
    return r;
  }

  private static @Ensures("IDLE") MultiTaskRobot switchArm(@Requires("IDLE") MultiTaskRobot r, String task) {
    r.unplugArm();
    if (task.equals("weld")) r.plugArm(new WelderArm());
    else if (task.equals("cut")) r.plugArm(new CutterArm());
    else r.plugArm(new BenderArm());
    return r;
  }

  private static @Ensures("NON_EMPTY") RobotGroup poweredRobotRobotGroup(int n_robot) {
    RobotGroup queue = new RobotGroup();
    do {
      Robot r = null;
      if (n_robot % 2 == 0) r = new BenderRobot();
      else r = new MultiTaskRobot(new CutterArm());
      n_robot--;
      r.turnOn();
      queue.add(r);
    } while (n_robot > 0);
    return queue;
  }

  private static List<String> initTasks(String... tasks) {
    List<String> taskList = new ArrayList<>();
    for (String task : tasks) taskList.add(task);
    return taskList;
  }
}
