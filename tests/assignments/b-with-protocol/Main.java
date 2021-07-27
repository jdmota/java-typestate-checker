public class Main {
  public static void main() {
    B b = new B();
    // :: warning: (b: State{B, Init})
    // :: error: (Cannot assign: cannot cast from State{B, Init} to Shared{A} | Null)
    A a = b;
  }

  public static void main2() {
    B b = new B();
    // :: warning: (b: State{B, Init})
    // :: error: (Incompatible parameter: cannot cast from State{B, Init} to Shared{A})
    play(b);
  }

  public static void play(A a) {

  }
}
