import jatyc.lib.Requires;

public class Main {
  public static void main1() {
    B b = new B();
    b.m1();
    A a = b; // Allowed, we are able to track the actual type and current state of the object
    B b2 = (B) a; // Allowed, we know this down-cast is safe since "a" is an instance of "B"
    b2.m2();
  }

  public static void main2() {
    B b = new B();
    b.m1();
    playA(b); // This is not allowed. The method expects an instance of "A" in state "StateA".
    // Incompatible parameter because State{B, StateB} is not a subtype of State{A, StateA}
  }

  public static void main3() {
    B b = new B();
    b.m1();
    playShared(b); // Allowed because this method only expects a "shared" object.
    b.m2(); // We still have ownership, let's finish the protocol
  }

  public static void playA(@Requires("StateA") A a) {
    a.m2();
  }

  public static void playShared(A a) {
    a.shared();
  }
}
