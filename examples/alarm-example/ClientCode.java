import jatyc.lib.*;

public class ClientCode {

  public void goodBehaviour() {
    double[] temperatures = {10.5, 20.5, 50.1, 100.0, 5.9, 10.4, 71.6};
    AlarmDevice a1 = connectToDevice(new AlarmDevice());
    AlarmDevice a2 = connectToDevice(new PredictiveAlarmDevice());
    for (double t : temperatures) {
      a2 = action(a2, t);
      a1 = action(a1, t);
    }
    a1.disconnect();
    a2.disconnect();
  }
  private @Ensures("CONN") AlarmDevice connectToDevice(@Requires("DISC") AlarmDevice device) {
    device.connect();
    device.setThreshold(50);
    if(device instanceof PredictiveAlarmDevice) {
      PredictiveAlarmDevice tmp = (PredictiveAlarmDevice) device;
      if (tmp.isTrainingNeeded()) tmp = modelUpdate(tmp);
      tmp.setInferenceTimeStep("1 hour");
      return tmp;
    }
    return device;
  }
  private @Ensures("CONN") PredictiveAlarmDevice modelUpdate(@Requires("DATA_VALIDATION") PredictiveAlarmDevice sd) {
    if (sd.dataValidation()) {
      sd.train();
      while (!sd.modelEvaluation()) {
        sd.modelTuning("some hyperparams");
        sd.train();
      }
    } else sd.pruneData();
    return sd;
  }

  private @Ensures("CONN") AlarmDevice action(@Requires("CONN") AlarmDevice a, double temp) {
    a.notify(temp);
    if (a.thresholdCheck() || (a instanceof PredictiveAlarmDevice && ((PredictiveAlarmDevice) a).predictiveThresholdCheck())) a.alert();
    return a;
  }

  /*public void badBehaviour() {
    AlarmDevice a1 = new AlarmDevice();
    AlarmDevice a2 = new SmartAlarmDevice();
    a1 = action2(a1, 10.5);
    a2 = action2(a2, 11.5);
  }

  private @Ensures("IDLE") AlarmDevice action2(@Requires("IDLE") AlarmDevice a, double temp) {
    a.notify(temp);
    if (a instanceof SmartAlarmDevice) {
      SmartAlarmDevice s = (SmartAlarmDevice) a;
      s.isTrainingNeeded();
      s = modelUpdate(s);
      return s;
    } else {
      if (a.thresholdCheck()) {}
      return a;
    }
  }*/

}
