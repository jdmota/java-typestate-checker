import jatyc.lib.Typestate;
import jatyc.lib.Anytime;

@Typestate("Dog")
public class Dog extends Animal {
  @Anytime
  public Sound sound() {
    // :: warning: (Sound.Bark: Shared{Sound})
    return Sound.Bark;
  }
  public void eat() {
    sound();
  }
  public void wag() {}
}
