import jatyc.lib.*;

public class ClientCode {

  private double temp_to_notify = 0.0;

  public void goodBehaviour() {
    temp_sensor_listening();
    double[] temperatures = {10.5, 20.5, 50.1, 100.0, 5.9, 10.4, 71.6};
    AlarmDevice a1 = new AlarmDevice();
    AlarmDevice a2 = new SmartAlarmDevice();
    for(double t : temperatures) {
      a2 = action(a2, t);
      a1 = action(a1, t);
    }
  }
  private @Ensures("IDLE") AlarmDevice action(@Requires("IDLE") AlarmDevice a, double temp) {
    a.notify(temp);
    if(a.thresholdCheck()) a.alert();
    if(a instanceof SmartAlarmDevice) {
      SmartAlarmDevice s = (SmartAlarmDevice) a;
      if(s.predictiveThresholdCheck("some time")) s.alert();
      if(s.isTrainingNeeded()) a = modelUpdate(s);
      else a = s;
    }
    return a;
  }

  private @Ensures("IDLE") SmartAlarmDevice modelUpdate(@Requires("DATA_VALIDATION") SmartAlarmDevice sd) {
    if (sd.dataValidation()){
      sd.train();
      while (!sd.modelEvaluation()) {
        sd.modelTuning("some hyperparams");
        sd.train();
      }
    } else sd.pruneData();
    return sd;
  }

  /*public void badBehaviour() {
    temp_sensor_listening();
    Observer o1 = new AlarmDevice();
    Observer o2 = new SmartDevice();
    o2 = action2(o2, temp_to_notify);
    o2.ack();
    o1 = action2(o1, temp_to_notify);
    o1.ack();
  }

  private @Ensures("ACK") Observer action2(@Requires("IDLE") Observer o, double temp) {
    o.notify(temp);
    if (o instanceof SmartDevice) {
      SmartDevice s = (SmartDevice) o;
      s.isTrainingNeeded();
      s = modelUpdate(s);
      temp_to_notify = s.forecast("some time");
      return s;
    } else {
      AlarmDevice a = (AlarmDevice) o;
      if (a.process()) {}
      return a;
    }
  }*/

  private void temp_sensor_listening() {
    // This method is used to listen to some temp sensors
    temp_to_notify = 45.5;
  }

}
