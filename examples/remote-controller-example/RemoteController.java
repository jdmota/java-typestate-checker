import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;
import java.util.*;

class RemoteController {
  public static void main(String[] args) {
    List<String> tasks = initTasks("weld", "task", "weld", "weld", "task");
    Robot r1 = new Robot();
    Robot r2 = new WeldingRobot();
    r1.start();
    r2.start();
    while (tasks.size() > 0) {
      String curr_task = tasks.remove(0);
      r1 = attemptTask(r1, curr_task);
      if(!r1.taskResult()) {
        r2 = attemptTask(r2, curr_task);
        if(!r2.taskResult()) tasks.add(curr_task);
      }
    }
    r1.stop();
    r2.stop();
  }

  private static @Ensures("IDLE") Robot attemptTask(@Requires("IDLE") Robot r, @Nullable String task) {
    switch(task) {
      case "weld":
        if(r instanceof WeldingRobot && !((WeldingRobot) r).weldMetal()) ((WeldingRobot) r).heating();
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




