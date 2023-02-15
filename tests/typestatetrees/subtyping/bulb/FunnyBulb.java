import jatyc.lib.Typestate;

@Typestate("FunnyBulb")
public class FunnyBulb extends Bulb {
  public boolean isFunnyMode() { return true; }
  public void funnyMode() {}
  public void stdMode() {}
  public void randomBrightness() {}
}
