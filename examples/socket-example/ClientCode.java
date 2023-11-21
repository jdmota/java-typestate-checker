import jatyc.lib.*;
import java.util.*;

class ClientCode {
  public static void main(String[] args) {
    List<String> data = initData("dataum","datum","datum","datum");
    Socket socket = new TimeoutSocket();
    if (socket.connect()) {
      while (data.size() > 0) {
        String datum = data.remove(0);
        if (datum == null) throw new RuntimeException();
        socket = forward(socket, datum);
      }
      socket.close();
    }
    System.out.println("Done!");
  }

  private static @Ensures("CONN") Socket forward(@Requires("CONN") Socket s, String datum) {
    if (s.canReceive()) {
      if (!(s instanceof TimeoutSocket) || !((TimeoutSocket) s).timeoutReceive()) s.receive();
      if (s.canSend(datum)) s.send(datum);
    }
    return s;
  }

  private static List<String> initData(String... data) {
    List<String> dataList = new ArrayList<>();
    for (String datum : data) dataList.add(datum);
    return dataList;
  }

}
