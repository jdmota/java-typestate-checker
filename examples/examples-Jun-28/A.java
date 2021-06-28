import jatyc.lib.Typestate;
import jatyc.lib.Anytime;

@Typestate("A")
public class A {
  public void m1() {}
  public void m2() {}
  
  @Anytime
  public void shared() {}
}
