package examples.Bookstore;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.ServerSocket;
import java.net.UnknownHostException;
import mungo.lib.Typestate;


@Typestate("Buyer1Protocol")
public class Buyer1Role{
	private BufferedReader socketSellerIn = null;
	private PrintWriter socketSellerOut = null;
	private BufferedReader socketBuyer2In = null;
	private PrintWriter socketBuyer2Out = null;
	public Buyer1Role() {
		// Connect to the other participants in the protocol
		try {
			// Create the sockets
			Socket socketSeller = new Socket("localhost", 20000);
			Socket socketBuyer2 = new Socket("localhost", 20002);
			socketSellerIn = new BufferedReader(new InputStreamReader(socketSeller.getInputStream()));
			socketSellerOut = new PrintWriter(socketSeller.getOutputStream(), true);
			socketBuyer2In = new BufferedReader(new InputStreamReader(socketBuyer2.getInputStream()));
			socketBuyer2Out = new PrintWriter(socketBuyer2.getOutputStream(), true);
		}
		catch(UnknownHostException e) {
			System.out.println("Unable to connect to the remote host");
			System.exit(-1);
		}
		catch (IOException e) {
			System.out.println("Input/output error");
			System.exit(-1);
		}
	}

	public void send_bookStringToSeller(String payload) {
		this.socketSellerOut.println(payload);
	}

	public int receive_bookintFromSeller() {
		String line = "";
		try {
			line  = this.socketSellerIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error.");
			System.exit(-1);
		}
		return Integer.parseInt(line);
	}

	public void send_quoteintToBuyer2(int payload) {
		this.socketBuyer2Out.println(payload);
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
			System.exit(-1);
		}
		return line;
	}

	public void send_transferintToSeller(int payload) {
		this.socketSellerOut.println(payload);
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
