import jatyc.lib.Typestate;

@Typestate("Car")
public class Car {
  public boolean turnOn() { return false; }
  public void setSpeed(int b) {}
  public void turnOff() {}
}
