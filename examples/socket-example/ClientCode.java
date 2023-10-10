import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;
import java.util.*;

//avoid referring to socket, but to higher level protocol?
class ClientCode {
  public static void main(String[] args) {
    List<String> data = initData("dataum","datum","datum","datum");
    Socket socket = new TimeoutSocket();
    if(socket.connect()) {
      while(data.size() > 0) {
        String datum = data.remove(0);
        socket = forward(socket, datum);
      }
      socket.close();
    }
  }


  /*private static @Ensures("CONN") Socket forward(@Requires("CONN") Socket s, @Nullable String datum) {
    if(s.canReceive(datum)) {
      if(s instanceof TimeoutSocket) {
        if(!((TimeoutSocket) s).timeoutReceive(datum)) s.receive(datum);
      } else s.receive(datum);
      if(s.canSend()) s.send();
    }
    return s;
  }*/


  //this does not compile
  private static @Ensures("CONN") Socket forward(@Requires("CONN") Socket s, @Nullable String datum) {
    if(s.canReceive(datum)) {
      if(!(s instanceof TimeoutSocket) || !((TimeoutSocket) s).timeoutReceive(datum)) s.receive(datum);
      if(s.canSend()) s.send();
    }
    return s;
  }





  private static List<String> initData(String... data) {
    List<String> dataList = new ArrayList<>();
    for (String datum : data) dataList.add(datum);
    return dataList;
  }

}




