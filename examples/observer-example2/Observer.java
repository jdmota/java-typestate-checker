import jatyc.lib.*;

@Typestate("ObserverProtocol")
public abstract class Observer {

  public Observer() {}
  public void notify(double temp) {}
  public abstract boolean isActionNeeded();
}
