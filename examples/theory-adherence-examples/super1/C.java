import jatyc.lib.*;

@Typestate("C")
public class C extends A {
  public void m1() {
    super.x.m();
  }
}
