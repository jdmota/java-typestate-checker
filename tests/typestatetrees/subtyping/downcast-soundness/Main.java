import jatyc.lib.Requires;

public class Main {
  public static void main() {
    C c = new C();
    // :: warning: (c: State{C, C1})
    c.m3();
    // :: warning: (c: State{C, C2})
    // :: error: (Incompatible parameter: cannot cast from State{C, C2} to State{A, A1})
    use(c);
  }

  public static void use(@Requires("A1") A a) {
    // :: warning: (a: State{A, A1})
    B b = (B) a;
    // :: warning: (b: State{B, B1})
    C c = (C) b;
    // :: warning: (c: State{C, C1})
    c.m2();
  }

  public static void use2(@Requires("A1") A a) {
    // :: warning: (a: State{A, A1})
    C c = (C) a;
    // :: warning: (c: State{C, C1})
    c.m2();
  }
}
