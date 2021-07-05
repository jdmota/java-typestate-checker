import jatyc.lib.Requires;

public class Main {
  public static void main1() {
    B b = new B();
    b.m1();
    A a = b; // error: Up-casting only allowed on initial or final states. Expected State{B, Init} | State{B, end} but got State{B, StateB}
    B b2 = (B) a;
    b2.m2();
  }

  public static void main2() {
    B b = new B();
    b.m1();
    playA(b); // error: Up-casting only allowed on initial or final states. Expected State{B, Init} | State{B, end} but got State{B, StateB}
  }

  public static void main3() {
    B b = new B();
    b.m1();
    playShared(b); // error: Up-casting only allowed on initial or final states. Expected State{B, Init} | State{B, end} but got State{B, StateB}
    b.m2();
  }

  public static void main4() {
    B b = new B();
    A a = b;
    a.m1();
    playA(a);
  }

  public static void main5() {
    B b = new B();
    b.m1();
    A a = b; // error: Up-casting only allowed on initial or final states. Expected State{B, Init} | State{B, end} but got State{B, StateB}
    playA(a);
  }

  public static void main6() {
    A a = new A();
    playShared(a); // error: Incompatible parameter because State{A, Init} is not a subtype of Shared{A}
  }

  public static void main7() {
    A a = new A();
    a.m1();
    a.m2();
    playShared(a);
  }

  public static void playA(@Requires("StateA") A a) {
    a.m2();
  }

  public static void playShared(A a) {
    a.shared();
  }
}
