import jatyc.lib.Typestate;

@Typestate("Animal")
public class Animal extends LivingBeing {
  private String type = "Animal";

  public Sound sound() {
    return Sound.GenericSound;
  }
  public void move() {}
  public void eat() {}

  public void getType() { System.out.println(type); }
}
