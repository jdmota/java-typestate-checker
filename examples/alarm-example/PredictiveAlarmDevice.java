import jatyc.lib.*;

@Typestate("PredictiveAlarmDeviceProtocol")
public class PredictiveAlarmDevice extends AlarmDevice {

  public PredictiveAlarmDevice() {}

  public boolean isTrainingNeeded() { return true; }
  public boolean predictiveThresholdCheck(String time) { return true; }
  public boolean dataValidation() { return true; }
  public void pruneData() {}
  public void train() {}
  public boolean modelEvaluation() { return true; }
  public void modelTuning(String hyperparms) {}

}
