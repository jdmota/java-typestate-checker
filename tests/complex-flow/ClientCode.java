import jatyc.lib.*;
import java.util.*;

class ClientCode {
  private static @Ensures("CONN") Socket forward(@Requires("CONN") Socket s, @Nullable String data) {
    // :: warning: (data: Shared{java.lang.String} | Null)
    // :: warning: (s: State{Socket, CONN})
    if (s.canReceive(data)) {
      // :: warning: (data: Shared{java.lang.String} | Null)
      // :: warning: (s: State{Socket, REC})
      // :: warning: (s: State{TimeoutSocket, REC})
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
        // :: warning: (s: State{TimeoutSocket, REC})
        if (!((TimeoutSocket) s).timeoutReceive(data)) {
          // :: warning: (data: Shared{java.lang.String} | Null)
          // :: warning: (s: State{TimeoutSocket, REC})
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

  private static void useStack(@Requires("UNKNOWN") Stack stack, List<String> tasks) {
    // :: warning: (stack: State{Stack, UNKNOWN})
    // :: warning: (tasks: Shared{java.util.List})
    while (!tasks.isEmpty() && !stack.isEmpty()) {
      // :: warning: (stack: State{Stack, NON_EMPTY})
      Socket s = stack.pop();
    }
    // :: warning: (stack: State{Stack, UNKNOWN})
    while (!stack.isEmpty()) {
      // :: warning: (stack: State{Stack, NON_EMPTY})
      Socket s = stack.pop();
    }
  }
}
