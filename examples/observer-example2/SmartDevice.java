import jatyc.lib.*;

@Typestate("SmartDeviceProtocol")
public class SmartDevice extends Observer {

  public SmartDevice() {}
  public boolean isActionNeeded() { return true; }
  public double forecast(String time) { return 0.0; }
  public boolean dataValidation() { return true; }
  public void pruneData() {}
  public void train() {}
  public boolean modelEvaluation() { return true; }
  public void modelTuning(String hyperparms) {}

}
