import jatyc.lib.Utils;

public class ClientCode {
  public static void example() {
    int x = 5;
    SUV[] suvs = new SUV[x];
    for (int i = 0; i < x; i++) {
      suvs[i] = new SUV();
      while (!suvs[i].turnOn()) { System.out.println("turning on..."); }
      suvs[i].switchMode();
      setSpeed(suvs[i]);
    }
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


