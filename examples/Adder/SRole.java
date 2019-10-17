package examples.Adder;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.ServerSocket;
import java.net.UnknownHostException;
import mungo.lib.Typestate;


@Typestate("SProtocol")
public class SRole{
	private BufferedReader socketCIn = null;
	private PrintWriter socketCOut = null;
	public SRole() {
		// Connect to the other participants in the protocol
		try {
			// Create the sockets
			Socket socketC = new Socket("localhost", 20000);
			socketCIn = new BufferedReader(new InputStreamReader(socketC.getInputStream()));
			socketCOut = new PrintWriter(socketC.getOutputStream(), true);
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

	public Choice1 receive_Choice1LabelFromC() {
		//receive ADD or BYE
		String stringLabelChoice1 = "";
		try {
			stringLabelChoice1 = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error, unable to get label");
			System.exit(-1);
		}
		int intLabelChoice1 = 0;
		if(stringLabelChoice1.equals("ADD")) {
			intLabelChoice1 = 1;
		}else if(stringLabelChoice1.equals("BYE")) {
			intLabelChoice1 = 2;
		}
		switch(intLabelChoice1) {
			case 1:
			return Choice1.ADD;
			case 2:
			default:
			return Choice1.BYE;
		}
	}

	public int receive_AddintFromC() {
		//receive integer to be added
		String line = "";
		try {
			line  = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error.");
			System.exit(-1);
		}
		return Integer.parseInt(line);
	}

	public int calculateResult(int first, int second) {
		int res = first + second;
		return res;
	}

	public void send_ResintToC(int payload) {
		//send result of addition
		this.socketCOut.println(payload);
	}

	public void receive_ByeFromC() {
		// Nothing to be received
		System.out.println("Goodbye.");
	}
}
