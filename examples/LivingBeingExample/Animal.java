import jatyc.lib.Typestate;
import jatyc.lib.Anytime;

@Typestate("Animal")
public class Animal extends LivingBeing {
  private String type = "Animal";

  @Anytime
  public Sound sound() {
    return Sound.GenericSound;
  }
  public void move() {}
  public void eat() {}

  @Anytime
  public void getType() { System.out.println(type); }
}
