import jatyc.lib.*;

@Typestate("AlarmDeviceProtocol")
public class AlarmDevice extends Observer {

  public AlarmDevice() {}
  public boolean isActionNeeded() {return true;}
  public void alert() {}

}
