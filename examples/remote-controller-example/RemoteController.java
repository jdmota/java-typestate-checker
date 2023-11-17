
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
  public static void goodBehaviour(@Requires("IDLE") Robot r1, @Requires("IDLE") Robot r2) {
    List<String> tasks = initTasks("weld", "cut", "bend", "weld", "bend");
    while (tasks.size() > 0) {
      String curr_task = tasks.remove(0);
      r1 = attemptTask(r1, curr_task);
      if (!r1.taskResult()) r2 = attemptTask(r2, curr_task);
    }
    r1.turnOff();
    r2.turnOff();
  }


  public static void upcastFails() {
    List<String> tasks = initTasks("weld", "cut", "bend", "weld", "bend");
    MultiTaskRobot r1 = new MultiTaskRobot(new CutterArm());
    r1.turnOn();
    while (tasks.size() > 0) {
      String curr_task = tasks.remove(0);
      r1.executeTask(curr_task);
      if(!r1.taskResult()) {
        r1 = switchArm(r1, curr_task);
        tasks.add(0, curr_task);
      }
    }
    r1.unplugArm();
    Robot r2 = new BenderRobot();
    r2.turnOn();
    goodBehaviour(r2,r1);
  }
  private static @Ensures("IDLE") Robot attemptTask(@Requires("IDLE") Robot r, @Nullable String task) {
    r.executeTask(task);
    if (!r.taskResult() && r instanceof MultiTaskRobot) {
      r = switchArm((MultiTaskRobot) r, task);
      r.executeTask(task);
    }
    return r;
  }
  private static @Ensures("IDLE") MultiTaskRobot switchArm(@Requires("IDLE") MultiTaskRobot r, @Nullable String task) {
    r.unplugArm();
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

