public class DroneTask {
  private final double x;
  private final double y;
  private final String task;

  public DroneTask(double x, double y, String task) {
    // :: warning: (this.x: Null)
    this.x = x;
    // :: warning: (this.y: Null)
    this.y = y;
    // :: warning: (this.task: Null)
    // :: warning: (task: Shared{java.lang.String})
    this.task = task;
  }

  public double getX() {
    return x;
  }

  public double getY() {
    return y;
  }

  public String getTask() {
    // :: warning: (this.task: Shared{java.lang.String})
    return task;
  }
}
