import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;

import mungo.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("CProtocol")
public class CRole {
  private BufferedReader socketSIn;
  private PrintWriter socketSOut;

  public CRole() {
    InetAddress addr;
    Socket socket = null;

    try {
      // :: warning: (addr: Null)
      addr = InetAddress.getByName("www.google.co.uk");
      // :: warning: (addr: Shared{java.net.InetAddress} | Null)
      if (addr == null) {
        throw new RuntimeException("Unable to listen on ports");
      }
      // :: warning: (socket: Null)
      // :: warning: (addr: Shared{java.net.InetAddress})
      socket = new Socket(addr, 80);
    } catch (Exception e) {
      System.out.println("Unable to listen on ports");
      System.exit(-1);
    }

    try {
      // :: warning: (this.socketSIn: Null)
      // :: warning: (socket: Shared{java.net.Socket})
      socketSIn = new BufferedReader(new InputStreamReader(socket.getInputStream()));
      // :: warning: (this.socketSOut: Null)
      // :: warning: (socket: Shared{java.net.Socket})
      socketSOut = new PrintWriter(socket.getOutputStream(), true);
    } catch (IOException e) {
      System.out.println("Read failed");
      System.exit(-1);
    }
  }

  public void send(String msg) {
    // :: warning: (this.socketSOut: Shared{java.io.PrintWriter})
    // :: warning: (msg: Shared{java.lang.String})
    this.socketSOut.print(msg);
  }

  public int receive() throws IOException {
    // :: warning: (this.socketSIn: Shared{java.io.BufferedReader})
    return this.socketSIn.read();
  }

  public void close() {

  }

}
