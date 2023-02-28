import jatyc.lib.Typestate;

@Typestate("FunnyBulb")
public class FunnyBulb extends Bulb {
  public boolean switchMode() { return true; }
  public void setColor(String color) {}
  public void randomColor() {}
}
