import jatyc.lib.*;

@Typestate("AutoDrivingCar")
public class AutoDrivingCar extends Car {

  private @Nullable AutoDriveAI driver;
  private Mode currMode;
  private int currSpeed;

  public AutoDrivingCar() {
    this.driver = null;
    this.currMode = Mode.MANUAL_DRIVE;
    this.currSpeed = 0;
  }

  public Mode switchMode() {
    if (currMode == Mode.AUTO_DRIVE) {
      driver = null;
      return Mode.MANUAL_DRIVE;
    }
    driver = new AutoDriveAI();
    return Mode.AUTO_DRIVE;
  }

  public void autoPark() {
    driver.park();
  }

  public void turnOff() {
    driver = null;
    currMode = Mode.MANUAL_DRIVE;
    currSpeed = 0;
  }

  public void setSpeed(int speed) {
    if (driver == null) currSpeed = speed;
    else currSpeed = driver.adjustSpeed(speed);
  }

}
