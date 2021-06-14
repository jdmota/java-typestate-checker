import jatyc.lib.Typestate;
import jatyc.lib.Anytime;

@Typestate("Animal")
public abstract class Animal extends LivingBeing {
  @Anytime
  public abstract Sound sound();
  public void move() {}
  public void eat() {}
}
