import jatyc.lib.*;

@Typestate("RobotProtocol")
public abstract class Robot {
  public Robot() {}
  public void turnOn() {}
  public void turnOff() {}
  public abstract void executeTask(String task);
  public boolean taskResult() {
    return true;
  }
}
