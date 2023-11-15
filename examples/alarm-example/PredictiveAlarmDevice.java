import jatyc.lib.*;

@Typestate("PredictiveAlarmDeviceProtocol")
public class PredictiveAlarmDevice extends AlarmDevice {

  public PredictiveAlarmDevice() {}

  public boolean isTrainingNeeded() { return true; }
  public boolean predictiveThresholdCheck() { return true; }
  public boolean dataValidation() { return true; }
  public void pruneData() {}
  public void setInferenceTimeStep(String timestep) {}
  public void train() {}
  public boolean modelEvaluation() { return true; }
  public void modelTuning(String hyperparms) {}

}
