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
        // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
        System.out.println("Unable to listen on ports");
        System.exit(-1);
      }
      // :: warning: (socket: Null)
      // :: warning: (addr: Shared{java.net.InetAddress})
      socket = new Socket(addr, 80);
    } catch (IOException e) {
      System.out.println("Unable to listen on ports");
      System.exit(-1);
    }

    try {
      // :: warning: (this.socketSIn: Null)
      // :: warning: (socket: NoProtocol{java.net.Socket, exact=true})
      socketSIn = new BufferedReader(new InputStreamReader(socket.getInputStream()));
      // :: warning: (this.socketSOut: Null)
      // :: warning: (socket: NoProtocol{java.net.Socket, exact=true})
      socketSOut = new PrintWriter(socket.getOutputStream(), true);
    } catch (IOException e) {
      System.out.println("Read failed");
      System.exit(-1);
    }
  }

  public void send(String msg) {
    // :: warning: (this.socketSOut: NoProtocol{java.io.PrintWriter, exact=true})
    // :: warning: (msg: Shared{java.lang.String})
    this.socketSOut.print(msg);
  }

  public int receive() throws IOException {
    // :: warning: (this.socketSIn: NoProtocol{java.io.BufferedReader, exact=true})
    return this.socketSIn.read();
  }

  public void close() {

  }

}
