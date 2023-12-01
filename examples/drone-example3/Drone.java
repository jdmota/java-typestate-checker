import jatyc.lib.*;

@Typestate("DroneProtocol")
public class Drone {
  public Drone() {}
  public void takeOff() {}
  public void shutDown() {}
  public void land() {}
  public void setDestination(double x, double y) {}
  public void takePicture() {}
  public boolean hasArrived() {
    return true;
  }
}
