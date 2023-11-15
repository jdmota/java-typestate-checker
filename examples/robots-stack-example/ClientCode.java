import jatyc.lib.*;
import java.util.*;

public class ClientCode {

  public void goodBehaviour() {
    Stack stack = poweredRobotStack(5);
    List<String> tasks = initTasks("weld", "move", "weld", "weld", "move");
    while(!tasks.isEmpty()) stack = executeTasks(stack,tasks);
    popAll(stack);
  }

  private @Ensures("UNKNOWN") Stack executeTasks(@Requires("UNKNOWN") Stack stack, List<String> tasks) {
    Stack auxiliaryStack = new Stack();
    while(!tasks.isEmpty() && !stack.isEmpty()) {
      String curr_task = tasks.remove(0);
      Robot r = attemptTask(stack.pop(), curr_task);
      if (!r.taskResult()) tasks.add(curr_task);
      auxiliaryStack.push(r);
    }
    while(!stack.isEmpty()) auxiliaryStack.push(stack.pop());
    return auxiliaryStack;
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

  private void popAll(@Requires("UNKNOWN") Stack stack) {
    while(!stack.isEmpty()) stack.pop().turnOff();
  }

  private @Ensures("UNKNOWN") Stack poweredRobotStack(int n_robot) {
    Stack stack = new Stack();
    for(int i = 0; i < n_robot; i++) {
      Robot r = null;
      if(i % 2 == 0) r = new Robot();
      else r = new WeldingRobot();
      r.turnOn();
      stack.push(r);
    }
    return stack;
  }

  private List<String> initTasks(String... tasks) {
    List<String> taskList = new ArrayList<>();
    for (String task : tasks) taskList.add(task);
    return taskList;
  }
}
