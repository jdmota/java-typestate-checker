import jatyc.lib.Requires;

public class ClientCode {
  public static void main(String[] args) {
    AutoDrivingCar car = new AutoDrivingCar();
    while (!car.turnOn()) { System.out.println("turning on..."); }
    setSpeedAndPark(car);
    System.out.println("Done!");
  }
  private static void setSpeedAndPark(@Requires("ON") Car c) {
    c.setSpeed(50);
    if (c instanceof AutoDrivingCar){
      ((AutoDrivingCar) c).autoPark();
    }
    c.turnOff();
  }
}
