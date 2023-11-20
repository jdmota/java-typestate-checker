import jatyc.lib.*;
import java.util.*;

class RemoteController {

  public static void main() {
    List<String> tasks = initTasks("weld", "cut", "bend", "weld", "bend");
    MultiTaskRobot r1 = new MultiTaskRobot(new CutterArm());
    r1.turnOn();
    r1 = sequentialTasksExecution(tasks, r1);
    r1.unplugArm();
    tasks = initTasks("weld", "cut", "bend", "weld", "bend");
    Robot r2 = new BenderRobot();
    parallelTasksExecution(tasks, r2, r1); //fixme what if the tasks are not completely done?
  }


  public static void parallelTasksExecution(List<String> tasks, @Requires("IDLE") Robot r1, @Requires("IDLE") Robot r2) {
    while (tasks.size() > 0) {
      String curr_task = tasks.remove(0);
      if (curr_task != null) {
        r1 = attemptTask(r1, curr_task);
        if (!r1.taskResult()) {
          r2 = attemptTask(r2, curr_task);
          if (!r2.taskResult()) tasks.add(curr_task);
        }
      }
    }
  }

  public static @Ensures("IDLE") Robot sequentialTasksExecution(List<String> tasks, @Requires("IDLE") Robot r) {
    int i = 0;
    while (i < tasks.size()) {
      String curr_task = tasks.get(i);
      i++;
      if (curr_task != null) {
        r1 = attemptTask(r1, curr_task);
        if (r1.taskResult()) tasks.remove(0);
      }
    }
    return r;
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

  private static List<String> initTasks(String... tasks) {
    List<String> taskList = new ArrayList<>();
    for (String task : tasks) taskList.add(task);
    return taskList;
  }
}
