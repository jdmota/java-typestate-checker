import jatyc.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("TimeoutSocketProtocol")
class TimeoutSocket extends Socket {
  public TimeoutSocket() {}

  public boolean timeoutReceive() { return true; }
}
