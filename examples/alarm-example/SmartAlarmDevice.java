import jatyc.lib.*;

@Typestate("SmartAlarmDeviceProtocol")
public class SmartAlarmDevice extends AlarmDevice {

  public SmartAlarmDevice() {}

  public boolean isTrainingNeeded() { return true; }
  public boolean predictiveThresholdCheck(String time) { return true; }
  public boolean dataValidation() { return true; }
  public void pruneData() {}
  public void train() {}
  public boolean modelEvaluation() { return true; }
  public void modelTuning(String hyperparms) {}

}
