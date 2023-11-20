import jatyc.lib.*;


@Typestate("QueueProtocol")
public class Queue {

  private @Nullable QueueNode fst;
  public Queue() {
    fst = null;
  }

  public void enqueue(@Requires("IDLE") Robot r) {
    QueueNode n = new QueueNode(r);
    if(fst == null) fst = n;
    else fst.setLast(n);
  }

  public @Ensures("IDLE") Robot dequeue() {
    Robot robot = fst.getElement();
    fst = fst.getNext();
    return robot;
  }
  public void turnAllOff() {
    while(fst != null) {
      Robot robot = fst.getElement();
      robot.turnOff();
      fst = fst.getNext();
    }
  }
}
