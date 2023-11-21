

public class DroneTask {

  private double x;
  private double y;

  private String task;
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
