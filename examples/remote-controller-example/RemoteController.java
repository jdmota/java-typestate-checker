import jatyc.lib.*;
import java.util.*;

class RemoteController {

  public static void goodBehaviour(@Requires("OFF") Robot r1, @Requires("OFF") Robot r2) {
    List<String> tasks = initTasks("weld", "move", "weld", "weld", "move");
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

  // TODO: tasks objects

  // Bad behavior: wrong method calls
  public static void badBehaviour1(@Requires("IDLE") Robot r) {
    List<String> tasks = initTasks("weld", "move", "weld", "weld", "move");
    while (tasks.size() > 0) {
      String curr_task = tasks.remove(0);
      switch (curr_task) {
        case "move":
          r.move(5.0, 0.0); // Problem: forgot to recharge if needed
          break;
        case "weld":
          if (r instanceof WeldingRobot) {
            WeldingRobot tmp = (WeldingRobot) r;
            if (!tmp.weldMetal()) tmp.heating();
            r = tmp;
          }
          break;
      }
      if (!r.taskResult()) tasks.add(curr_task);
    }
    r.turnOff();
  }

  // Bad behavior: upcast fails
  public static void badBehaviour2(@Requires("IDLE") Robot r) {
    List<String> tasks = initTasks("weld", "move", "weld", "weld", "move");
    while (tasks.size() > 0) {
      String curr_task = tasks.remove(0);
      switch (curr_task) {
        case "move":
          if (!r.move(5.0, 0.0)) r.recharge();
          break;
        case "weld":
          if (r instanceof WeldingRobot) {
            ((WeldingRobot) r).weldMetal(); // Problem: forgot to reheat if needed
          }
          break;
      }
      if (!r.taskResult()) tasks.add(curr_task);
    }
    r.turnOff();
  }

  // Good behavior
  private static @Ensures("IDLE") Robot attemptTask(@Requires("IDLE") Robot r, @Nullable String task) {
    switch (task) {
      case "weld":
        if (r instanceof WeldingRobot) {
          WeldingRobot tmp = (WeldingRobot) r;
          if (!tmp.weldMetal()) tmp.heating();
          r = tmp;
        }
        break;
      case "move":
        if (!r.move(5.0, 0.0)) r.recharge();
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
