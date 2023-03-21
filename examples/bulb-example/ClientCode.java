import jatyc.lib.Requires;

public class ClientCode {
  public static void example() {
    FunnyBulb f = new FunnyBulb();
    while (!f.connect()) { System.out.println("connecting..."); }
    f.switchMode();
    setBrightness(f);
  }

  private static void setBrightness(@Requires("CONN") Bulb b) {
    if (b instanceof FunnyBulb && ((FunnyBulb) b).switchMode() == Mode.RND) {
      ((FunnyBulb) b).randomColor();
    }
    b.setBrightness(10);
    b.disconnect();
  }
}
