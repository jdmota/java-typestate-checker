import jatyc.lib.Requires;
import jatyc.lib.Ensures;

public class ClientCode {
  public static void example1() {
    FunnyBulb b = new FunnyBulb();
    // :: warning: (b: State{FunnyBulb, DISCONN})
    // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
    while (!b.connect()) { System.out.println("connecting..."); }
    // :: warning: (b: State{FunnyBulb, STD_CONN})
    b.switchMode();
    // :: warning: (b: State{FunnyBulb, FUNNY_CONN} | State{FunnyBulb, STD_CONN})
    setBrightness(b);
  }

  private static void setBrightness(@Requires("CONN") Bulb b) {
    // :: warning: (b: State{Bulb, CONN})
    // :: warning: (b: State{FunnyBulb, FUNNY_CONN} | State{FunnyBulb, STD_CONN})
    if (b instanceof FunnyBulb && ((FunnyBulb) b).switchMode()) {
      // :: warning: (b: State{FunnyBulb, FUNNY_CONN})
      ((FunnyBulb) b).randomColor();
    }
    // :: warning: (b: State{Bulb, CONN})
    b.setBrightness(10);
    // :: warning: (b: State{Bulb, CONN})
    b.disconnect();
  }
}
