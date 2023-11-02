import jatyc.lib.*;

public class ClientCode {

  public void goodBehaviour() {
    double[] temperatures = {10.5, 20.5, 50.1, 100.0, 5.9, 10.4, 71.6};
    AlarmDevice a1 = new AlarmDevice();
    AlarmDevice a2 = new SmartAlarmDevice();
    for (double t : temperatures) {
      a2 = action(a2, t);
      a1 = action(a1, t);
    }
  }

  private @Ensures("IDLE") AlarmDevice action(@Requires("IDLE") AlarmDevice a, double temp) {
    a.notify(temp);
    if (a.thresholdCheck()) a.alert();
    if (a instanceof SmartAlarmDevice) {
      SmartAlarmDevice s = (SmartAlarmDevice) a;
      if (s.predictiveThresholdCheck("some time")) s.alert();
      if (s.isTrainingNeeded()) a = modelUpdate(s);
      else a = s;
    }
    return a;
  }

  private @Ensures("IDLE") SmartAlarmDevice modelUpdate(@Requires("DATA_VALIDATION") SmartAlarmDevice sd) {
    if (sd.dataValidation()) {
      sd.train();
      while (!sd.modelEvaluation()) {
        sd.modelTuning("some hyperparams");
        sd.train();
      }
    } else sd.pruneData();
    return sd;
  }

  public void badBehaviour() {
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
  }

}
