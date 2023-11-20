import jatyc.lib.*;

@Typestate("MultiTaskRobotProtocol")
public class MultiTaskRobot extends Robot {

  @Nullable MechanicalArm arm;
  public MultiTaskRobot(MechanicalArm a) {
    super();
    arm = a;
  }

  //overriding
  public void executeTask(String task) {
    arm.use();
  }

  public void unplugArm() {
    arm = null;
  }

  public void plugArm(MechanicalArm a) {
    arm = a;
  }
}
