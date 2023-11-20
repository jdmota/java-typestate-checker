import jatyc.lib.*;

@Typestate("WeldingRobotProtocol")
public class WeldingRobot extends Robot {
  private @Nullable Welder welder;

  public WeldingRobot() {
    super();
    this.welder = new Welder();
  }

  public void turnOn() {
    // overriding
  }

  public boolean weldMetal() {
    return this.welder.use();
  }

  public void reheat() {
    this.welder.reheat();
  }

  public void addWelder(@Requires("USE") Welder w) {
    this.welder = w;
  }

  public @Ensures("USE") Welder removeWelder() {
    Welder w = this.welder;
    this.welder = null;
    return w;
  }
}
