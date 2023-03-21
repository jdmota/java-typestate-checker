import jatyc.lib.Typestate;

@Typestate("FunnyBulb")
public class FunnyBulb extends Bulb {
  public Mode switchMode() { return Mode.RND; }
  public void setColor(String color) {}
  public void randomColor() {}
}
