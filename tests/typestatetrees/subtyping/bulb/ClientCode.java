import jatyc.lib.Requires;
import jatyc.lib.Ensures;

public class ClientCode {
  public static void example1() {
    FunnyBulb b = new FunnyBulb();
    // :: warning: (b: State{FunnyBulb, DISCONN})
    // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
    while (!b.connect()) { System.out.println("connecting..."); }
    // :: warning: (b: State{FunnyBulb, STD_CONN})
    setBrightness(b);
  }

  public static void example2() {
    FunnyBulb b = new FunnyBulb();
    // :: warning: (b: State{FunnyBulb, DISCONN})
    // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
    while (!b.connect()) { System.out.println("connecting..."); }
    // :: warning: (b: State{FunnyBulb, STD_CONN})
    b.funnyMode();
    // :: warning: (b: State{FunnyBulb, FUNNY_CONN})
    setBrightness(b);
  }

  private static void setBrightness(@Requires("CONN") Bulb b) {
    // :: warning: (b: State{Bulb, CONN})
    if (b instanceof FunnyBulb) {
      // :: warning: (b: State{Bulb, CONN})
      FunnyBulb fb = (FunnyBulb) b;
      // :: warning: (fb: State{FunnyBulb, FUNNY_CONN} | State{FunnyBulb, STD_CONN})
      if (fb.isFunnyMode()) {
        // :: warning: (fb: State{FunnyBulb, FUNNY_CONN})
        fb.randomBrightness();
      } else {
        // :: warning: (fb: State{FunnyBulb, STD_CONN})
        fb.setBrightness(10);
      }
      // :: warning: (fb: State{FunnyBulb, FUNNY_CONN} | State{FunnyBulb, STD_CONN})
      // :: warning: (b: Shared{Bulb})
      b = fb;
    } else {
      // :: warning: (b: State{Bulb, CONN})
      b.setBrightness(10);
    }
    // :: warning: (b: State{Bulb, CONN})
    b.disconnect();
  }

  private static void setBrightness2(@Requires("CONN") Bulb b) {
    // :: warning: (b: State{Bulb, CONN})
    if (b instanceof FunnyBulb) {
      // :: warning: (b: State{Bulb, CONN})
      if (((FunnyBulb) b).isFunnyMode()) {
        // :: warning: (b: State{Bulb, CONN})
        ((FunnyBulb) b).randomBrightness();
      } else {
        // :: warning: (b: State{Bulb, CONN})
        b.setBrightness(10);
      }
    } else {
      // :: warning: (b: State{Bulb, CONN})
      b.setBrightness(10);
    }
    // :: warning: (b: State{Bulb, CONN})
    b.disconnect();
  }

  private static void setBrightness3(@Requires("CONN") Bulb b) {
    // :: warning: (b: State{Bulb, CONN})
    if (b instanceof FunnyBulb && ((FunnyBulb) b).isFunnyMode()) {
      // :: warning: (b: State{Bulb, CONN})
      ((FunnyBulb) b).randomBrightness();
    } else {
      // :: warning: (b: State{Bulb, CONN})
      b.setBrightness(10);
    }
    // :: warning: (b: State{Bulb, CONN})
    b.disconnect();
  }

  public static void example3() {
    FunnyBulb b = new FunnyBulb();
    // :: warning: (b: State{FunnyBulb, DISCONN})
    // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
    while (!b.connect()) { System.out.println("connecting..."); }
    // :: warning: (b: State{FunnyBulb, STD_CONN})
    b.funnyMode();
    // :: warning: (b: State{FunnyBulb, FUNNY_CONN})
    setBrightness4(b);
    // :: warning: (b: State{FunnyBulb, FUNNY_CONN} | State{FunnyBulb, STD_CONN})
    b.disconnect();
  }

  private static void setBrightness4(final @Requires("CONN") @Ensures("CONN") Bulb b) {
    // :: warning: (b: State{Bulb, CONN})
    if (b instanceof FunnyBulb && ((FunnyBulb) b).isFunnyMode()) {
      // :: warning: (b: State{Bulb, CONN})
      ((FunnyBulb) b).randomBrightness();
    } else {
      // :: warning: (b: State{Bulb, CONN})
      b.setBrightness(10);
    }
  }
}
