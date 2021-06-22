import jatyc.lib.Typestate;
import jatyc.lib.Anytime;

@Typestate("Dog")
public class Dog extends Animal {
  @Anytime
  public Sound sound() { return Sound.Bark; }
  @Anytime
  public void roll() { }
  public void eat() {
    sound();
  }
  public void wag() {}
}
