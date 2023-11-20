import jatyc.lib.*;
import java.util.*;

public class ClientCode {

  public void goodBehaviour() {
    Queue queue = poweredRobotQueue(5);
    List<String> tasks = initTasks("weld", "move", "weld", "weld", "move");
    while(!tasks.isEmpty()) {
      String curr_task = tasks.remove(0);
      Robot r = attemptTask(queue.dequeue(), curr_task);
      if (!r.taskResult()) tasks.add(curr_task);
      queue.enqueue(r);
    }
    queue.turnAllOff();
  }

  private @Ensures("IDLE") Robot attemptTask(@Requires("IDLE") Robot r, @Nullable String task) {
    switch (task) {
      case "weld":
        if (r instanceof WeldingRobot) {
          WeldingRobot w = (WeldingRobot) r;
          if (!w.weldMetal()) w.reheat();
          r = w;
        }
        break;
      case "move":
        if (!r.move(5.0, 0.0)) r.recharge();
        break;
    }
    return r;
  }
  private @Ensures("NON_EMPTY") Queue poweredRobotQueue(int n_robot) {
    Queue queue = new Queue();
    do {
      Robot r = null;
      if(n_robot % 2 == 0) r = new Robot();
      else r = new WeldingRobot();
      n_robot--;
      r.turnOn();
      queue.enqueue(r);
    } while(n_robot > 0);
    return queue;
  }

  private List<String> initTasks(String... tasks) {
    List<String> taskList = new ArrayList<>();
    for (String task : tasks) taskList.add(task);
    return taskList;
  }
}
