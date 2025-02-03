import jatyc.lib.*;

@Typestate("C")
public class C extends A {
  X x;
  public C() {
    x = new X();
  }
  public void m1() {

    x.m();
    int y = super.x;

  }
}
