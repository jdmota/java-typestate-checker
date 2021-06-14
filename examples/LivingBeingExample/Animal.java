import mungo.lib.Typestate;
@Typestate("Animal.protocol")
public class Animal extends LivingBeing {
  public Sound sound() {return Sound.GenericSound;}
  public void move() {}
  public void eat() {}
}
