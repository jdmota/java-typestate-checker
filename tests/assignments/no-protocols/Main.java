public class Main {
  public static void main1() {
    B b = new B();
    // :: warning: (b: Shared{B})
    A a = b;
  }

  public static void main2() {
    B b = new B();
    // :: warning: (b: Shared{B})
    play(b);
  }

  public static void play(A a) {

  }
}
