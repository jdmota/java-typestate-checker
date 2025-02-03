import jatyc.lib.*;

@Typestate("A")
public class A {
  public void m1() {
    A a = new A();
    a.m1();
  }
}
