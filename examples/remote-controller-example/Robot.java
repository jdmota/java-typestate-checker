import jatyc.lib.Typestate;

@Typestate("RobotProtocol")
class Robot {
  public Robot() { }

  public void start() { }

  public void stop() { }

  public boolean task() {return true; }

  public void recharge() { }

  public boolean taskResult() {return true;}
}
