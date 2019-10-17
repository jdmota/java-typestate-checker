package examples.BuyTicket;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.ServerSocket;
import java.net.UnknownHostException;
import mungo.lib.Typestate;


@Typestate("AProtocol")
public class ARole{
	private BufferedReader socketRIn = null;
	private PrintWriter socketROut = null;
	private BufferedReader socketFIn = null;
	private PrintWriter socketFOut = null;
	public ARole() {
		// Bind the sockets
		ServerSocket serverF = null;
		try {// Create the sockets
		serverF = new ServerSocket(20002);
		}
		catch (IOException e) {
			System.out.println("Unable to listen on port");
			System.exit(-1);
		}
		// Accept a client connection
		Socket socketF = null;
		try {
			System.out.println("Accepting...");
			socketF = serverF.accept();
		}

		catch (IOException e) {

			System.out.println("Accept failed");
			System.exit(-1);
		}
		// Create the Finance read and write streams
		try {
			socketFIn = new BufferedReader(new InputStreamReader(socketF.getInputStream()));
			socketFOut = new PrintWriter(socketF.getOutputStream(), true);
		}
		catch (IOException e) {
			System.out.println("Read failed");
			System.exit(-1);
		}
		System.out.println("Accepted connection");
		// Connect to the servers
		try {// Create the sockets
		Socket socketR = new Socket("localhost", 20001);
		// Create the Researcher read and write streams
		socketRIn = new BufferedReader(new InputStreamReader(socketR.getInputStream()));
		socketROut = new PrintWriter(socketR.getOutputStream(), true);
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

	public String receive_requestStringFromR() {
		String line = "";
		try {
			line  = this.socketRIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error.");
			System.exit(-1);
		}
			return line;
	}

	public void send_quoteintToR(int payload) {
			this.socketROut.println(payload);
	}

	public Choice1 receive_Choice1LabelFromF() {
		String stringLabelChoice1 = "";
		try {
			stringLabelChoice1 = this.socketFIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error, unable to get label");
			System.exit(-1);
		}
		int intLabelChoice1 = 0;
		if(stringLabelChoice1.equals("APPROVE")) {
			intLabelChoice1 = 1;
		}else if(stringLabelChoice1.equals("REFUSE")) {
			intLabelChoice1 = 2;
		}
		switch(intLabelChoice1) {
			case 1:
			return Choice1.APPROVE;
			case 2:
			default:
			return Choice1.REFUSE;
		}
	}

	public int receive_approveintFromF() {
		String line = "";
		try {
			line  = this.socketFIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error.");
			System.exit(-1);
		}
		return Integer.parseInt(line);
	}

	public void send_ticketStringToR(String payload) {
		this.socketROut.println(payload);
	}

	public void send_invoiceintToF(int payload) {
		this.socketFOut.println(payload);
	}

	public int receive_paymentintFromF() {
		String line = "";
		try {
			line  = this.socketFIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error.");
			System.exit(-1);
		}
		return Integer.parseInt(line);
	}

	public String receive_refuseStringFromF() {
		String line = "";
		try {
			line  = this.socketFIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error.");
			System.exit(-1);}
		return line;
		}
	}
