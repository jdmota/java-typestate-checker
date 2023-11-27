import jatyc.lib.*;

@Typestate("RobotProtocol")
class BenderRobot extends Robot {
  private MechanicalArm arm;

  public BenderRobot() {
    arm = new BenderArm();
  }

  public void executeTask(String task) {
    arm.use();
  }
}
