import jatyc.lib.Requires;

public class Main {
  // :: error: ([a2] did not complete its protocol (found: State{A, S1}))
  public static void main1() {
    A a = new A();
    // :: warning: (a: State{A, S1})
    A a2 = a;
  }

  // :: error: ([a] did not complete its protocol (found: State{A, S1}))
  public static void main2() {
    B b = new B();
    // :: warning: (b: State{B, S1})
    A a = b;
  }

  // :: error: ([a] did not complete its protocol (found: State{A, S1}))
  public static void main3() {
    B b = new B();
    // :: warning: (b: State{B, S1})
    b.m2();
    // :: warning: (b: State{B, S2})
    A a = b;
  }

  public static void main4() {
    B b = new B();
    // :: warning: (b: State{B, S1})
    b.m();
    // :: warning: (b: State{B, end})
    A a = b;
  }

  public static void main5() {
    A a = new A();
    // :: warning: (a: State{A, S1})
    // :: error: (Incompatible parameter: cannot cast from State{A, S1} to Shared{A})
    play1(a);
  }

  public static void main6() {
    A a = new A();
    // :: warning: (a: State{A, S1})
    play2(a);
  }

  public static void main7() {
    B b = new B();
    // :: warning: (b: State{B, S1})
    play2(b);
  }

  public static void main8() {
    B b = new B();
    // :: warning: (b: State{B, S1})
    b.m2();
    // :: warning: (b: State{B, S2})
    play2(b);
  }

  public static void main9() {
    B b = new B();
    // :: warning: (b: State{B, S1})
    b.m();
    // :: warning: (b: State{B, end})
    play1(b);
  }

  public static void play1(A a) {

  }

  public static void play2(@Requires("S1") A a) {
    // :: warning: (a: State{A, S1})
    a.m();
  }
}
