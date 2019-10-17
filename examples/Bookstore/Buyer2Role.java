package examples.Bookstore;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.ServerSocket;
import java.net.UnknownHostException;
import mungo.lib.Typestate;


@Typestate("Buyer2Protocol")
public class Buyer2Role{
	private BufferedReader socketSellerIn = null;
	private PrintWriter socketSellerOut = null;
	private BufferedReader socketBuyer1In = null;
	private PrintWriter socketBuyer1Out = null;
	public Buyer2Role() {
		// Bind the sockets
		ServerSocket serverBuyer1 = null;
		try {// Create the sockets
			serverBuyer1 = new ServerSocket(20002);
		}
		catch (IOException e) {
			System.out.println("Unable to listen on port");
			System.exit(-1);
		}
		// Accept a client connection
		Socket socketBuyer1 = null;
		try {
			System.out.println("Accepting...");
			socketBuyer1 = serverBuyer1.accept();
		}

		catch (IOException e) {

			System.out.println("Accept failed");
			System.exit(-1);
		}
		// Create the read and write streams
		try {
			socketBuyer1In = new BufferedReader(new InputStreamReader(socketBuyer1.getInputStream()));
			socketBuyer1Out = new PrintWriter(socketBuyer1.getOutputStream(), true);
		}
		catch (IOException e) {
			System.out.println("Read failed");
			System.exit(-1);
		}
		System.out.println("Accepted connection");
		// Connect to the servers
		try {// Create the sockets
			Socket socketSeller = new Socket("localhost", 20001);
			// Create the read and write streams
			socketSellerIn = new BufferedReader(new InputStreamReader(socketSeller.getInputStream()));
			socketSellerOut = new PrintWriter(socketSeller.getOutputStream(), true);
		}
		catch(UnknownHostException e) {
			System.out.println("Unable to connect to the remote host");
			System.exit(-1);
		}
		catch (IOException e) {
			System.out.println("Input/output error, unable to connect");
			System.exit(-1);
		}
	}

	public int receive_quoteintFromBuyer1() {
		String line = "";
		try {
			line  = this.socketBuyer1In.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error.");
			System.exit(-1);
		}
		return Integer.parseInt(line);
	}

	public void send_AGREEToBuyer1() {
		this.socketBuyer1Out.println("AGREE");
		this.socketSellerOut.println("AGREE"); //also send to seller
	}

	public void send_QUITToBuyer1() {
		this.socketBuyer1Out.println("QUIT");
		this.socketSellerOut.println("QUIT"); //also send to seller
	}

	public void send_agreeStringToBuyer1(String payload) {
		this.socketBuyer1Out.println(payload);
	}

	public void send_agreeStringToSeller(String payload) {
		this.socketSellerOut.println(payload);
		/* Added to avoid the "Send transfer"
		message appearing on both Buyer1 and Buyer2 terminals at once.*/
		String ok = "";
		try {
			ok = this.socketSellerIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error");
			System.exit(-1);
		}
	}

	public void send_transferintToSeller(int payload) {
		this.socketSellerOut.println(payload);
	}

	public void send_quitStringToBuyer1(String payload) {
		this.socketBuyer1Out.println(payload);
	}

	public void send_quitStringToSeller(String payload) {
		this.socketSellerOut.println(payload);
	}
}
