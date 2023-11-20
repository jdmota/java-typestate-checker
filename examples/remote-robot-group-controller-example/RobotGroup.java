import jatyc.lib.*;

@Typestate("RobotGroupProtocol")
public class RobotGroup {
  private @Nullable RobotNode fst;

  public RobotGroup() {
    fst = null;
  }

  public void add(@Requires("IDLE") Robot r) {
    RobotNode n = new RobotNode(r);
    if (fst == null) fst = n;
    else fst.setLast(n);
  }

  public @Ensures("IDLE") Robot take() {
    return fst.take();
  }

  public void putBack(@Requires("IDLE") Robot r) {
    fst.putBack(r);
  }

  public void next() {
    RobotNode n = fst;
    fst = n.getNext();

    if (fst == null) fst = n;
    else fst.setLast(n);
  }

  public void turnAllOff() {
    while (fst != null) {
      Robot robot = fst.take();
      robot.turnOff();
      fst = fst.getNext();
    }
  }
}
