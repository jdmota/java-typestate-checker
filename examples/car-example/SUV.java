import jatyc.lib.Typestate;

@Typestate("SUV")
public class SUV extends Car {

  private final int THRESHOLD = 80;
  private Mode mode;
  private boolean ecoDrive;
  private boolean fourWheels;
  private int speed;

  public SUV() {
    this.mode = Mode.COMFORT;
    this.ecoDrive = false;
    this.fourWheels = false;
    this.speed = 0;
  }
  public Mode switchMode() {
    if(mode == Mode.SPORT) {
      mode = Mode.COMFORT;
      fourWheels = false;
    }
    else {
      mode = Mode.SPORT;
      ecoDrive = false;
    }
    return mode;
  }
  public void setEcoDrive(boolean state) {
    ecoDrive = state;
  }
  public void setFourWheels(boolean state) {
    fourWheels = state;
  }

//override
  public void setSpeed(int b) {
    if(ecoDrive) speed = b < THRESHOLD ? b : THRESHOLD;
    else speed = b;
  }
}
