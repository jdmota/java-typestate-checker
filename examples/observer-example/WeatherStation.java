import jatyc.lib.*;

public class WeatherStation {

  private double temp_to_notify = 0.0;

  public void goodBehaviour() {
    temp_sensor_listening();
    Observer o1 = new AlarmDevice();
    Observer o2 = new SmartDevice();
    o2 = action(o2, temp_to_notify);
    o2.ack();
    o1 = action(o1, temp_to_notify);
    o1.ack();
  }

  private @Ensures("ACK") Observer action(@Requires("IDLE") Observer o, double temp) {
    o.notify(temp);
    if (o instanceof SmartDevice) {
      SmartDevice tmp = (SmartDevice) o;
      if(tmp.isTrainingNeeded()) tmp = modelUpdate(tmp);
      temp_to_notify = tmp.forecast("some time");
      return tmp;
    } else {
      AlarmDevice tmp = (AlarmDevice) o;
      if(tmp.process()) tmp.alert();
      return tmp;
    }
  }

  private @Ensures("NOTIFIED") SmartDevice modelUpdate(@Requires("DATA_VALIDATION") SmartDevice sd) {
    if(sd.dataValidation()){
      sd.train();
      while(!sd.modelEvaluation()) {
        sd.modelTuning("some hyperparams");
        sd.train();
      }
    } else sd.pruneData();
    return sd;
  }

  /*public void badBehaviour() {
    temp_sensor_listening();
    Observer o1 = new AlarmDevice();
    o1.notify(temp_to_notify);
    if (o1 instanceof AlarmDevice) o1 = action2((AlarmDevice) o1);
    o1.ack();
  }*/

  /*private @Ensures({"ALERT", "NOTIFIED"}) AlarmDevice action2(@Requires("NOTIFIED") AlarmDevice o) {
    if (o.process()) {}
    return o;
  }*/

  private void temp_sensor_listening() {
    // This method is used to listen to some temp sensors
    temp_to_notify = 45.5;
  }

}
