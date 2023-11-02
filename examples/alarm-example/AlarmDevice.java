import jatyc.lib.*;

@Typestate("AlarmDeviceProtocol")
public class AlarmDevice {

  public AlarmDevice() {}

  public void notify(double val) {}
  public boolean thresholdCheck() {return true;}
  public void alert() {}

}
