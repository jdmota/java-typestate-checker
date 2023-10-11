import jatyc.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("SocketProtocol")
class Socket {
  public Socket() {}

  public boolean connect() { return true; }

  public void send(String datum) {}

  public boolean canReceive() { return true; }

  public boolean canSend(String datum) { return true; }

  public String receive() {return "";}

  public void close() {}
}
