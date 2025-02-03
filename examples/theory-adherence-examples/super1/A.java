import jatyc.lib.*;

@Typestate("A")
public class A {
  X x;
  public A() {
    x = new X();
  }

  public void m1() {
  }
}
