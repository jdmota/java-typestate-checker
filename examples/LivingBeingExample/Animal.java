import mungo.lib.Typestate;

@Typestate("Animal")
public abstract class Animal extends LivingBeing {
  public abstract Sound sound();
  public void move() {}
  public void eat() {}
}
