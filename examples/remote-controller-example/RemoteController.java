
import jatyc.lib.*;
import java.util.*;

class RemoteController {

  /*public static void goodBehaviour(@Requires("OFF") Robot r1, @Requires("OFF") Robot r2) {
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

  // Good behavior
  private static @Ensures("IDLE") Robot attemptTask(@Requires("IDLE") Robot r, @Nullable String task) {
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
            WeldingRobot w = (WeldingRobot) r;
            if (!w.weldMetal()) w.reheat(); // Problem: forgot to recharge in previous loop
            r = w;
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

  // Bad behavior: upcast fails
  public static void badBehaviour3(@Requires("IDLE") Robot r) {
    List<String> tasks = initTasks("weld", "move", "weld", "weld", "move");
    while (tasks.size() > 0) {
      String curr_task = tasks.remove(0);
      switch (curr_task) {
        case "move":
          if (!r.move(5.0, 0.0)) r.recharge();
          break;
        case "weld":
          if (r instanceof WeldingRobot) {
            WeldingRobot w = (WeldingRobot) r;
            if (!w.weldMetal()) w.reheat();
            w.removeWelder();
            r = w; // Problem: forgot to readd the welder before upcasting
          }
          break;
      }
      if (!r.taskResult()) tasks.add(curr_task);
    }
    r.turnOff();
  }*/
  public static void upcastFails() {
    List<String> tasks = initTasks("weld", "cut", "bend", "weld", "bend");
    Robot r1 = new BenderRobot();
    Robot r2 = new MultiTaskRobot(new CutterArm());
    r1.turnOn();
    r2.turnOn();
    while (tasks.size() > 0) {
      String curr_task = tasks.remove(0);
      r1 = attemptTask(r1, curr_task);
      if (!r1.taskResult()) {
        r2 = attemptTask(r2, curr_task);
        ((MultiTaskRobot) r2).unplugArm(); //upcast fails
      }
    }
    r1.turnOff();
    r2.turnOff();
  }
  private static @Ensures("IDLE") Robot attemptTask(@Requires("IDLE") Robot r, @Nullable String task) {
    r.executeTask(task);
    if (!r.taskResult() && r instanceof MultiTaskRobot) {
      MultiTaskRobot multiTaskRobot = (MultiTaskRobot) r;
      multiTaskRobot.unplugArm();
      multiTaskRobot = plugArm(multiTaskRobot, task);
      multiTaskRobot.executeTask(task);
      r = multiTaskRobot;
    }
    return r;
  }
  private static @Ensures("IDLE") MultiTaskRobot plugArm(@Requires("UNPLUGGED") MultiTaskRobot r, @Nullable String task) {
    if(task.equals("weld")) r.plugArm(new WelderArm());
    else if(task.equals("cut")) r.plugArm(new CutterArm());
    else r.plugArm(new BenderArm());
    return r;
  }


  private static List<String> initTasks(String... tasks) {
    List<String> taskList = new ArrayList<>();
    for (String task : tasks) taskList.add(task);
    return taskList;
  }

}

