public class Main {
  public static void main1(String[] args) throws Exception {
    Animal x = new Dog();
    x.move();
    m1(x);
    LivingBeing x1 = x;
    ((Dog) x1).wag();
    x1.sound();
  }

  public static void m1(LivingBeing x) {
    if (x instanceof Dog) ((Dog) x).roll();
    else x.sound();
  }
}
