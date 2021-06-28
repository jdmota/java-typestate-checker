import jatyc.lib.Requires;

public class Main {
  public static void main1() {
    B b = new B();
    b.m1();
    B b2 = b;
    A a = b;
    a.shared();
    b2.m2();
  }

  public static void main2() { // :: error: [b2] did not complete its protocol (found: State{B, StateB})
    B b = new B();
    b.m1();
    B b2 = b;
    A a = b;
    a.shared();
    B b3 = (B) a;
    b3.m2(); // :: error: Cannot call [m2] on Shared{B}
  }

  public static void main3() {
    B b = new B();
    b.m1();
    B b2 = b;
    A a = b;
    a.shared();
    B b3 = (B) b2;
    b3.m2();
  }

  public static void main4() {
    B b = new B();
    b.m1();
    A a = b;
    playA(a); // :: error: Incompatible parameter because State{B, StateB} is not a subtype of State{A, StateA}
  }

  public static void main5() {
    B b = new B();
    b.m1();
    A a = b;
    playB((B) a);
  }

  public static void main6() {
    B b = new B();
    play(b);
    b.m1();
    b.m2();
  }

  public static void playA(@Requires("StateA") A a) {
    a.m2();
  }

  public static void playB(@Requires("StateB") B b) {
    b.m2();
  }

  public static void play(A a) {
    a.shared();
  }
}
