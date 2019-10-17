package examples.BuyTicket;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.ServerSocket;
import java.net.UnknownHostException;
import mungo.lib.Typestate;

@Typestate("FProtocol")
public class FRole{
	private BufferedReader socketRIn = null;
	private PrintWriter socketROut = null;
	private BufferedReader socketAIn = null;
	private PrintWriter socketAOut = null;
	public FRole() {
		// Connect to the other participants in the protocol
		try {
			// Create the sockets
			Socket socketR = new Socket("localhost", 20000);
			Socket socketA = new Socket("localhost", 20002);
			socketRIn = new BufferedReader(new InputStreamReader(socketR.getInputStream()));
			socketROut = new PrintWriter(socketR.getOutputStream(), true);
			socketAIn = new BufferedReader(new InputStreamReader(socketA.getInputStream()));
			socketAOut = new PrintWriter(socketA.getOutputStream(), true);
		}
		catch(UnknownHostException e) {
			System.out.println("Unable to connect to the remote host");
			System.exit(-1);
		}
		catch (IOException e) {
			System.out.println("Input/output error");
			System.exit(-1);
		}
		System.out.println("Connected");
	}

	public int receive_checkintFromR() {
		String line = "";
		try {
			line  = this.socketRIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error.");
			System.exit(-1);
		}
		return Integer.parseInt(line);
	}

	public void send_APPROVEToR() {
		this.socketROut.println("APPROVE");
		this.socketAOut.println("APPROVE"); //also send to Agent
	}

	public void send_REFUSEToR() {
		this.socketROut.println("REFUSE");
		this.socketAOut.println("REFUSE"); //also send to Agent
	}

	public void send_approveintToR(int payload) {
		this.socketROut.println(payload);
	}

	public void send_approveintToA(int payload) {
		this.socketAOut.println(payload);
	}

	public int receive_invoiceintFromA() {
		String line = "";
		try {
		 line  = this.socketAIn.readLine();
	}
		catch(IOException e) {
			System.out.println("Input/Output error.");
			System.exit(-1);
		}
		return Integer.parseInt(line);
	}

	public void send_paymentintToA(int payload) {
		this.socketAOut.println(payload);
	}

	public void send_refuseStringToR(String payload) {
		this.socketROut.println(payload);
	}

	public void send_refuseStringToA(String payload) {
		this.socketAOut.println(payload);
	}
}
