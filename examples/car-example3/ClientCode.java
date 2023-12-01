import jatyc.lib.Requires;

public class ClientCode {
  public static void main(String[] args) {
    SUV sc = new SUV();
    while (!sc.turnOn()) { System.out.println("turning on..."); }
    sc.switchMode();
    switchSUVAndSetSpeed(sc);
    System.out.println("Done!");
  }
  private static void switchSUVAndSetSpeed(@Requires("ON") Car c) {
    if (c instanceof SUV && ((SUV) c).switchMode() == Mode.SPORT){
      ((SUV) c).setFourWheels(true);
    }
    c.turnOff();
    c.setSpeed(50);
  }
}
