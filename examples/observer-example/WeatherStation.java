
import jatyc.lib.*;

public class WeatherStation {

  private double temp_to_notify = 0.0;

  public void goodBehaviour() {
    temp_sensor_listening();
    Observer o1 = new AlarmDevice();
    Observer o2 = new SmartDevice();
    String time = "some time";
    o2.notify(temp_to_notify);
    if(o2 instanceof SmartDevice) o2 = action((SmartDevice) o2, time);
    o2.ack();
    o1.notify(temp_to_notify);
    if(o1 instanceof AlarmDevice) o1 = action((AlarmDevice) o1);
    o1.ack();
  }

  private @Ensures("ACK") Observer action(@Requires("NOTIFIED") SmartDevice o, String curr_time) {
    if(o.isTrainingNeeded()) o.train();
    temp_to_notify = o.forecast(curr_time);
    return o;
  }

  private @Ensures("ACK") Observer action(@Requires("NOTIFIED") AlarmDevice o) {
    if(o.process()) o.alert();
    return o;
  }

  private void temp_sensor_listening() {
    /*this method is used to listen to some temp sensors*/
    temp_to_notify = 45.5;
  }

}
