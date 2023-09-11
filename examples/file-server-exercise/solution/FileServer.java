import java.net.*;
import java.io.*;
import jatyc.lib.Typestate;

@Typestate("FileServer")
public class FileServer {
  private Socket socket;
  protected OutputStream out;
  protected BufferedReader in;
  protected String lastFilename;

  public boolean start(Socket s) {
    try {
      socket = s;
      out = socket.getOutputStream();
      in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
      return true;
    } catch (Exception e) {
      e.printStackTrace();
      return false;
    }
  }

  public boolean hasRequest() throws Exception {
    String command = in.readLine();
    if (command != null && command.equals("REQUEST")) {
      String filename = in.readLine();
      if (filename != null) {
        lastFilename = filename;
        return true;
      }
    }
    return false;
  }

  public String receiveFilename() throws Exception {
    return lastFilename;
  }

  public void sendEof() throws Exception {
    out.write(0);
    out.flush();
  }

  public void sendByte(int b) throws Exception {
    out.write(b);
  }

  public void close() throws Exception {
    in.close();
    out.close();
    socket.close();
  }

  public static void main(String[] args) throws Exception {
    ServerSocket serverSocket = new ServerSocket(1234);
    while (true) {
      new FileServerThread(serverSocket.accept()).start();
    }
  }
}
