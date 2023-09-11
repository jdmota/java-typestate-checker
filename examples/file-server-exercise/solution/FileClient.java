import java.net.*;
import java.io.*;
import jatyc.lib.Typestate;

@Typestate("FileClient")
public class FileClient {
  private Socket socket;
  protected OutputStream out;
  protected BufferedReader in;
  protected int lastByte;

  public boolean start() {
    try {
      socket = new Socket("localhost", 1234);
      out = socket.getOutputStream();
      in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
      return true;
    } catch (Exception e) {
      e.printStackTrace();
      return false;
    }
  }

  public void request(String filename) throws Exception {
    out.write("REQUEST\n".getBytes());
    out.write(filename.getBytes());
    out.write('\n');
    out.flush();
    lastByte = in.read();
  }

  public boolean hasNextByte() {
    return lastByte != 0;
  }

  public int nextByte() throws Exception {
    int b = lastByte;
    lastByte = in.read();
    return b;
  }

  public void close() throws Exception {
    out.write("CLOSE\n".getBytes());
    out.flush();
    // 
    in.close();
    out.close();
    socket.close();
  }

  public static void main(String[] args) throws Exception {
    FileClient client = new FileClient();
    if (client.start()) {
      System.out.println("File client started!");
      client.request("hello.txt");
      System.out.println("File contents:");
      while (client.hasNextByte()) {
        System.out.print((char) client.nextByte());
      }
      client.close();
    } else {
      System.out.println("Could not start client!");
    }
  }
}
