import jatyc.lib.*;
import java.util.*;

class ClientCode {
  public static void main(String[] args) {
    List<String> dataList = new ArrayList<>();
    Socket socket = new TimeoutSocket();
    // :: warning: (socket: State{Socket, DISC})
    if (socket.connect()) {
      // :: warning: (dataList: Shared{java.util.List})
      while (dataList.size() > 0) {
        // :: warning: (dataList: Shared{java.util.List})
        String data = dataList.remove(0);
        // :: warning: (socket: State{Socket, CONN})
        // :: warning: (data: Shared{java.lang.String} | Null)
        socket = forward(socket, data);
      }
      // :: warning: (socket: State{Socket, CONN})
      socket.close();
    }
  }

  private static @Ensures("CONN") Socket forward(@Requires("CONN") Socket s, @Nullable String data) {
    // :: warning: (data: Shared{java.lang.String} | Null)
    // :: warning: (s: State{Socket, CONN})
    if (s.canReceive(data)) {
      // :: warning: (data: Shared{java.lang.String} | Null)
      // :: warning: (s: State{Socket, REC})
      if (!(s instanceof TimeoutSocket) || !((TimeoutSocket) s).timeoutReceive(data)) {
        // :: warning: (data: Shared{java.lang.String} | Null)
        // :: warning: (s: State{Socket, REC})
        s.receive(data);
      }
      // :: warning: (s: State{Socket, SEND})
      // :: warning: (s: State{Socket, CONN})
      if (s.canSend()) s.send();
    }
    // :: warning: (s: State{Socket, CONN})
    return s;
  }

  private static @Ensures("CONN") Socket forward2(@Requires("CONN") Socket s, @Nullable String data) {
    // :: warning: (data: Shared{java.lang.String} | Null)
    // :: warning: (s: State{Socket, CONN})
    if (s.canReceive(data)) {
      // :: warning: (s: State{Socket, REC})
      if (s instanceof TimeoutSocket) {
        // :: warning: (data: Shared{java.lang.String} | Null)
        // :: warning: (s: State{Socket, REC})
        if (!((TimeoutSocket) s).timeoutReceive(data)) {
          // :: warning: (data: Shared{java.lang.String} | Null)
          // :: warning: (s: State{Socket, REC})
          s.receive(data);
        }
      } else {
        // :: warning: (data: Shared{java.lang.String} | Null)
        // :: warning: (s: State{Socket, REC})
        s.receive(data);
      }
      // :: warning: (s: State{Socket, SEND})
      // :: warning: (s: State{Socket, CONN})
      if (s.canSend()) s.send();
    }
    // :: warning: (s: State{Socket, CONN})
    return s;
  }
}
