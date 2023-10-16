import jatyc.lib.*;

@Typestate("SmartDeviceProtocol")
public class SmartDevice extends Observer {

  public SmartDevice() {}
  public boolean isTrainingNeeded() {return true;}
  public double forecast(String time) {return 0.0;}
  public void train() {}


}
