package examples.Bookstore;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.ServerSocket;
import java.net.UnknownHostException;
import mungo.lib.Typestate;


@Typestate("SellerProtocol")
public class SellerRole{
	private BufferedReader socketBuyer2In = null;
	private PrintWriter socketBuyer2Out = null;
	private BufferedReader socketBuyer1In = null;
	private PrintWriter socketBuyer1Out = null;
	public SellerRole() {
		// Bind the sockets
		ServerSocket serverBuyer2 = null;
		ServerSocket serverBuyer1 = null;
		// Connecting to the server
		try {// Create the sockets
			serverBuyer2 = new ServerSocket(20001);
			serverBuyer1 = new ServerSocket(20000);
		}
		catch(IOException e) {
			System.out.println("Unable to listen on ports");
			System.exit(-1);
		}
		// Accept a client connection
		Socket socketBuyer2 = null;
		Socket socketBuyer1 = null;
		try {
			System.out.println("Accepting...");
			socketBuyer2 = serverBuyer2.accept();
			System.out.println("Buyer2 accepted");
			System.out.println("Accepting...");
			socketBuyer1 = serverBuyer1.accept();
			System.out.println("Buyer1 accepted");
		}
		catch (IOException e) {
			System.out.println("Accept failed");
			System.exit(-1);
		}
		// Create the read and write streams
		try {
			socketBuyer2In = new BufferedReader(new InputStreamReader(socketBuyer2.getInputStream()));
			socketBuyer2Out = new PrintWriter(socketBuyer2.getOutputStream(), true);
			socketBuyer1In = new BufferedReader(new InputStreamReader(socketBuyer1.getInputStream()));
			socketBuyer1Out = new PrintWriter(socketBuyer1.getOutputStream(), true);
		}
		catch (IOException e) {
			System.out.println("Read failed");
			System.exit(-1);
		}
	}

	public String receive_bookStringFromBuyer1() {
		String line = "";
		try {
			line  = this.socketBuyer1In.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error.");
			System.exit(-1);
		}
		return line;
	}

	public void send_bookintToBuyer1(int payload) {
		this.socketBuyer1Out.println(payload);
	}

	public Choice1 receive_Choice1LabelFromBuyer2() {
		String stringLabelChoice1 = "";
		try {
			stringLabelChoice1 = this.socketBuyer2In.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error, unable to get label");
			System.exit(-1);
		}
		int intLabelChoice1 = 0;
		if(stringLabelChoice1.equals("AGREE")) {
			intLabelChoice1 = 1;
			System.out.println("Buyer2 Agrees");
		}else if(stringLabelChoice1.equals("QUIT")) {
			intLabelChoice1 = 2;
			System.out.println("Buyer2 Refuses");
		}
		switch(intLabelChoice1) {
			case 1:
			return Choice1.AGREE;
			case 2:
			default:
			return Choice1.QUIT;
		}
	}

	public String receive_agreeStringFromBuyer2() {
		String line = "";
		try {
			line  = this.socketBuyer2In.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error.");
		System.exit(-1);}
		return line;
	}

	public int receive_transferintFromBuyer1() {
		String line = "";
		try {
			line  = this.socketBuyer1In.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error.");
			System.exit(-1);
		}
		/* Added to avoid the "Send transfer"
		message appearing on both Buyer1 and Buyer2 terminals at once.*/
		this.socketBuyer2Out.println("OK Buyer2");
		return Integer.parseInt(line);
	}

	public int receive_transferintFromBuyer2() {
		String line = "";
		try {
			line  = this.socketBuyer2In.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error.");
			System.exit(-1);
		}
		return Integer.parseInt(line);
	}

	public String receive_quitStringFromBuyer2() {
		String line = "";
		try {
			line  = this.socketBuyer2In.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error.");
			System.exit(-1);
		}
		return line;
	}
}
