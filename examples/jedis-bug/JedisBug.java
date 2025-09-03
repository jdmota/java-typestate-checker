import java.io.IOException;
import java.io.PrintStream;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.List;
import java.util.Set;
import redis.clients.jedis.Client;
import redis.clients.jedis.Pipeline;
import redis.clients.jedis.Response;

public class JedisBug {

  public static void main(String[] args) {
    String to = args[0];
    String bug = args[1];
    int timeout = 1000;
    int bugNo = 1;
    if (to != null) timeout = Integer.parseInt(to);
    if (bug != null) bugNo = Integer.parseInt(bug);

    System.out.println("Running with timeout:" + timeout + " and bugNo:" + bugNo);

    Thread serverThread = new Thread(() -> JedisBug.serverLoop());
    serverThread.start();

    try (Client jedis = new Client("localhost", 8123)) {
      jedis.setConnectionTimeout(timeout);
      jedis.setSoTimeout(timeout);
      if (bugNo == 1) {
        firstBug(jedis);
      } else if (bugNo == 2) {
        secondBug(jedis);
      } else {
        throw new IllegalArgumentException("Wrong bug number " + bugNo);
      }
    }
  }

  private static void firstBug(Client jedis) {
    // same buggy behavior as before
    jedis.zrevrange("somekey", 0, 1);
    final List<String> result = jedis.getMultiBulkReply();
    System.err.println("Received: " + result);
  }

  private static void secondBug(Client jedis) {
    try (Pipeline pipeline = new Pipeline()) {
      pipeline.setClient(jedis);
      Response<Set<String>> response = pipeline.zrevrange("somekey", 0, 1);
      pipeline.sync();
      System.err.println("Received: " + response.get());
    } catch (Exception e) {
      e.printStackTrace();
    }
  }

  private static void serverLoop() {
    try {
      ServerSocket server = new ServerSocket(8123);

      Socket socket = server.accept();

      String response1 = "*1\r\n$11\r\n*";
      String response2 = "*800000000\r\n";

      PrintStream printStream = new PrintStream(socket.getOutputStream());
      printStream.append(response1);
      printStream.flush();
      Thread.sleep(2000);
      printStream.append(response2);
      printStream.close();
      System.out.println("Exiting server");
    } catch (IOException | InterruptedException e) {
      System.err.println("Got exception: " + e);
    }
  }
}
