public class DroneTask {
  private final double x;
  private final double y;
  private final String task;

  public DroneTask(double x, double y, String task) {
    this.x = x;
    this.y = y;
    this.task = task;
  }

  public double getX() {
    return x;
  }

  public double getY() {
    return y;
  }

  public String getTask() {
    return task;
  }
}
