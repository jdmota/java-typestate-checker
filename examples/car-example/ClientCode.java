import jatyc.lib.Requires;

public class ClientCode {
  public static void example() {
    SUV sc = new SUV();
    while (!sc.turnOn()) { System.out.println("turning on..."); }
    sc.switchMode();
    switchSUVAndSetSpeed(sc);
  }

  private static void switchSUVAndSetSpeed(@Requires("ON") Car c) {
    if (c instanceof SUV && ((SUV) c).switchMode() == Mode.SPORT){
      ((SUV) c).setFourWheels(true);
    }
    c.setSpeed(50);
    c.turnOff();
  }
}
