import java.util.*;

public class RemoteController {
  public static void main() {
    List<String> tasks = new ArrayList<>();
    Robot r1 = new WeldingRobot();
    // :: warning: (r1: State{Robot, OFF})
    r1.turnOn();
    // :: warning: (tasks: Shared{java.util.List})
    while (tasks.size() > 0) {
      // :: warning: (r1: State{Robot, IDLE})
      // :: error: Cannot perform upcast on [(WeldingRobot) r1] from State{WeldingRobot, HEAT} | State{WeldingRobot, IDLE} to class [Robot] after call
      if (r1 instanceof WeldingRobot) ((WeldingRobot) r1).weldMetal();
    }
    // :: warning: (r1: State{Robot, IDLE})
    r1.turnOff();
  }
}
