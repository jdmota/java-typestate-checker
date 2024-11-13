public class Main {
  //not correct: a.m1 is unreachable
  public static void main(String[] args) {
    A a = new A();
    return ;
    a.m1();
  }

  //this is correct (works as in the theory)
  public static void main2(String[] args) {
    A a = new A();
    if (a.m1()) {
      return;
    } else a.m2();
  }
}
