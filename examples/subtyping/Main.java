public class Main {
  public static void main(String[] args) {
    Base o = new Derived();
    while (o.offer1() == Status.NO) {
      o.offer2();
    }
    o.done();
  }
}
