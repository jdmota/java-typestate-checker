import mungo.lib.Typestate;

@Typestate("Dog")
public class Dog extends Animal {
  public Sound sound() {return Sound.Bark;}
  public void eat() {sound();}
  public void wag() {}
}
