import jatyc.lib.*;

@Typestate("DroneProtocol")
public class Drone {
  public Drone() {}
  public void takeOff() {}
  public void shutDown() {}
  public void land() {}
  public void moveTo(double x, double y) {}
  public void takePicture() {}
  public void stop() {}
  public boolean hasArrived() {
    return true;
  }
}
