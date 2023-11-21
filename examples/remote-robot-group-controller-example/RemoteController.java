import jatyc.lib.*;
import java.util.*;

class RemoteController {
  public static void useMultipleRobot() {
    List<String> tasks = initTasks("weld", "cut", "bend", "weld", "bend");
    RobotGroup group = poweredRobotGroup(4);
    while (!tasks.isEmpty()) {
      String curr_task = tasks.remove(0);
      if (curr_task != null) {
        Robot r = attemptTask(group.take(), curr_task);
        if (!r.taskResult()) tasks.add(curr_task);
        group.putBack(r);
        group.next();
      }
    }
    group.turnAllOff();
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

  private static @Ensures("NON_EMPTY") RobotGroup poweredRobotGroup(int n_robot) {
    RobotGroup group = new RobotGroup();
    do {
      Robot r = null;
      if (n_robot % 2 == 0) r = new BenderRobot();
      else r = new MultiTaskRobot(new CutterArm());
      n_robot--;
      r.turnOn();
      group.add(r);
    } while (n_robot > 0);
    return group;
  }

  private static List<String> initTasks(String... tasks) {
    List<String> taskList = new ArrayList<>();
    for (String task : tasks) taskList.add(task);
    return taskList;
  }
}
