import jatyc.lib.*;
import java.util.*;

class RemoteController {
  public static void goodBehaviour() {
    List<String> tasks = initTasks("weld", "task", "weld", "weld", "task");
    Robot r1 = new Robot();
    Robot r2 = new WeldingRobot();
    r1.turnOn();
    r2.turnOn();
    while (tasks.size() > 0) {
      String curr_task = tasks.remove(0);
      r1 = attemptTask(r1, curr_task);
      if (!r1.taskResult()) {
        r2 = attemptTask(r2, curr_task);
        if (!r2.taskResult()) tasks.add(curr_task);
      }
    }
    r1.turnOff();
    r2.turnOff();
  }

  public static void badBehaviour() {
    List<String> tasks = initTasks("weld", "task", "weld", "weld", "task");
    Robot r1 = new WeldingRobot();
    r1.turnOn();
    while (tasks.size() > 0) {
      String curr_task = tasks.remove(0);
      switch(curr_task) {
        case "task":
          r1.task();
          break;
        case "weld":
          if (r1 instanceof WeldingRobot) ((WeldingRobot) r1).weldMetal();
          break;
      }
      if (!r1.taskResult()) tasks.add(curr_task);
    }
    r1.turnOff();
  }

  private static @Ensures("IDLE") Robot attemptTask(@Requires("IDLE") Robot r, @Nullable String task) {
    switch(task) {
      case "weld":
        if (r instanceof WeldingRobot && !((WeldingRobot) r).weldMetal()) ((WeldingRobot) r).heating();
        break;
      case "task":
        if(!r.task()) r.recharge();
        break;
    }
    return r;
  }

  private static List<String> initTasks(String... tasks) {
    List<String> taskList = new ArrayList<>();
    for (String task : tasks) taskList.add(task);
    return taskList;
  }
}
