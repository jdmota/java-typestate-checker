import jatyc.lib.Typestate;

@Typestate("SUV")
public class SUV extends Car {
  public Mode switchMode() { return Mode.SPORT; }
  public void setEcoDrive(boolean state) {}
  public void setFourWheels(boolean state) {}
}
