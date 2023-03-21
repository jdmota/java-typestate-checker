import jatyc.lib.Typestate;

@Typestate("Bulb")
public class Bulb {
  public boolean connect() { return false; }
  public void setBrightness(int b) {}
  public void disconnect() {}
}
