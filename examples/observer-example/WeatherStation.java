import jatyc.lib.*;

public class WeatherStation {

  private double temp_to_notify = 0.0;

  public void goodBehaviour() {
    temp_sensor_listening();
    Observer o1 = new AlarmDevice();
    Observer o2 = new SmartDevice();
    o2 = action(o2, temp_to_notify);
    o1 = action(o1, temp_to_notify);
  }

  private @Ensures("IDLE") Observer action(@Requires("IDLE") Observer o, double temp) {
    o.notify(temp);
    if (o instanceof SmartDevice) {
      SmartDevice s = (SmartDevice) o;
      s.ack();
      if (s.isTrainingNeeded()) s = modelUpdate(s);
      temp_to_notify = s.forecast("some time");
      return s;
    } else {
      AlarmDevice a = (AlarmDevice) o;
      if (a.process()) a.alert();
      a.ack();
      return a;
    }
  }

  private @Ensures("IDLE") SmartDevice modelUpdate(@Requires("DATA_VALIDATION") SmartDevice sd) {
    if (sd.dataValidation()){
      sd.train();
      while (!sd.modelEvaluation()) {
        sd.modelTuning("some hyperparams");
        sd.train();
      }
    } else sd.pruneData();
    return sd;
  }

  public void badBehaviour() {
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
  }

  private void temp_sensor_listening() {
    // This method is used to listen to some temp sensors
    temp_to_notify = 45.5;
  }

}
