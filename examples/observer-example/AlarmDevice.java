import jatyc.lib.*;

@Typestate("AlarmDeviceProtocol")
public class AlarmDevice extends Observer {

  public AlarmDevice() {}
  public boolean process() {return true;}
  public void alert() {}

}
