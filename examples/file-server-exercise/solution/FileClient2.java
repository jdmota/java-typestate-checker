import java.net.*;
import java.io.*;
import jatyc.lib.Typestate;

@Typestate("FileClient2")
public class FileClient2 extends FileClient {

  public String nextLine() throws Exception {
    StringBuilder str = new StringBuilder();

    while (lastByte != 10 && lastByte != 0) {
      str.append((char) lastByte);
      lastByte = in.read();
    }

    if (lastByte == 10) {
      lastByte = in.read();
    }

    return str.toString();
  }

  public static void main(String[] args) throws Exception {
    FileClient2 client = new FileClient2();
    if (client.start()) {
      System.out.println("File client started!");
      client.request("hello.txt");
      System.out.println("File lines:");
      while (client.hasNextByte()) {
        System.out.println(client.nextLine());
      }
      client.close();
    } else {
      System.out.println("Could not start client!");
    }
  }
}
