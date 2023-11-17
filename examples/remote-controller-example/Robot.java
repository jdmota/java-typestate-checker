import jatyc.lib.*;

@Typestate("RobotProtocol")
abstract class Robot {
  public Robot() {}
  public void turnOn() {}
  public void turnOff() {}
  public abstract void executeTask(@Nullable String task);
  public boolean taskResult() {
    return true;
  }
}
