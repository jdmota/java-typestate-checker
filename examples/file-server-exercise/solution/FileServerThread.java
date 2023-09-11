import java.net.*;

public class FileServerThread extends Thread {
  private Socket socket;

  public FileServerThread(Socket socket) {
    this.socket = socket;
  }

  public void run() {
    try {
      FileServer server = new FileServer();
      if (server.start(socket)) {
        System.out.println("File server started!");
        while (server.hasRequest()) {
          String filename = server.receiveFilename();

          server.sendByte((byte)'H');
          server.sendByte((byte)'E');
          server.sendByte((byte)'L');
          server.sendByte((byte)'L');
          server.sendByte((byte)'O');
          server.sendByte((byte)'\n');
          server.sendByte((byte)'W');
          server.sendByte((byte)'O');
          server.sendByte((byte)'R');
          server.sendByte((byte)'L');
          server.sendByte((byte)'D');
          server.sendByte((byte)'!');
          server.sendByte((byte)'\n');
          server.sendEof();
        }
        server.close();
      } else {
        System.out.println("Could not start server!");
      }
    } catch (Exception e) {
      e.printStackTrace();
    }
  }
}
