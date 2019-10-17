package examples.Adder;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.ServerSocket;
import java.net.UnknownHostException;
import mungo.lib.Typestate;

@Typestate("CProtocol")
public class CRole{
	private BufferedReader socketSIn = null;
	private PrintWriter socketSOut = null;
	public CRole() {
		// Bind the sockets
		ServerSocket serverS = null;
		// Connecting to the server
		try {// Create the sockets
			serverS = new ServerSocket(20000);
		}
		catch(IOException e) {
			System.out.println("Unable to listen on ports");
			System.exit(-1);
		}
		// Accept a client connection
		Socket socketS = null;
		try {
			System.out.println("Accepting...");
			socketS = serverS.accept();
			System.out.println("S accepted");
		}
		catch (IOException e) {
			System.out.println("Accept failed");
			System.exit(-1);
		}
		// Create the read and write streams
		try {
			socketSIn = new BufferedReader(new InputStreamReader(socketS.getInputStream()));
			socketSOut = new PrintWriter(socketS.getOutputStream(), true);
		}
		catch (IOException e) {
			System.out.println("Read failed");
			System.exit(-1);
		}
	}

	public void send_ADDToS() {
		//send ADD label
		this.socketSOut.println("ADD");
	}

	public void send_BYEToS() {
		//send BYE label
		this.socketSOut.println("BYE");
	}

	public void send_AddintToS(int payload) {
		//send integer to be added
		this.socketSOut.println(payload);
	}

	public int receive_ResintFromS() {
		//receive result of addition
		String line = "";
		try {
			line  = this.socketSIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error.");
			System.exit(-1);
		}
		return Integer.parseInt(line);
	}

	public void send_ByeToS() {
		// Nothing to be sent
		System.out.println("Goodbye.");
	}
}
