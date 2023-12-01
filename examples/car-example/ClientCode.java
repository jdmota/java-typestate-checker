public class ClientCode {
  public static void example() {
    SUV suv = new SUV();
    while (!suv.turnOn()) { System.out.println("turning on..."); }
    suv.switchMode();
    setSpeed(suv);
  }
  private static void setSpeed(@jatyc.lib.Requires("ON") Car car) {
    if (car instanceof SUV && ((SUV) car).switchMode() == Mode.SPORT)
      ((SUV) car).setFourWheels(true);
    car.setSpeed(50);
    car.turnOff();
  }

  public static void main(String[] args) {
    example();
    System.out.println("Done!");
  }
}
