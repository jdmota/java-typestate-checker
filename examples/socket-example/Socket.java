import jatyc.lib.Typestate;
import jatyc.lib.Nullable;


@Typestate("SocketProtocol")
class Socket {
  public Socket() {}

  public boolean connect() {return true;}

  public void send() {}

  public boolean canReceive(@Nullable String datum) {return true;}

  public boolean canSend() {return true;}

  public void receive(@Nullable String datum) { }

  public void close() {}

}
