import jatyc.lib.*;
import java.util.*;

class RemoteController {

  public static void main() {
    List<String> tasks = initTasks("weld", "cut", "bend", "weld", "bend");
    MultiTaskRobot r1 = new MultiTaskRobot(new CutterArm());
    r1.turnOn();
    r1 = (MultiTaskRobot) sequentialTasksExecution(tasks, r1);
    r1.unplugArm();
    List<String> tasks1 = initTasks("weld", "cut", "bend", "weld", "bend");
    List<String> tasks2 = initTasks("weld", "cut", "bend", "weld", "bend");
    Robot r2 = new BenderRobot();
    r2.turnOn();
    r1 = (MultiTaskRobot) sequentialTasksExecution(tasks1, r1); //errors: typestate upcast fails
    r2 = sequentialTasksExecution(tasks2, r2);
    r1.turnOff();
    r2.turnOff();
  }
  public static @Ensures("IDLE") Robot sequentialTasksExecution(List<String> tasks, @Requires("IDLE") Robot r) {
    int i = 0;
    while (i < tasks.size()) {
      String curr_task = tasks.get(i);
      i++;
      if (curr_task != null) {
        r = attemptTask(r, curr_task);
        if(r.taskResult()) tasks.remove(0);
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
