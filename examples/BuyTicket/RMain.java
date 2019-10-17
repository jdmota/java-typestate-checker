package examples.BuyTicket;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.ServerSocket;
import java.net.UnknownHostException;


public class RMain {
	public static String safeRead(BufferedReader readerR) {
		String readline = "";
		try {
			readline = readerR.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error, unable to read");
			System.exit(-1);
		}
		return readline;
	}
	public static void main(String[] args) {
		// Create the current role
		RRole currentR =  new RRole();
		// readerR can be used to input strings, and then use them in send method invocation
		BufferedReader readerR = new BufferedReader(new InputStreamReader(System.in));
		// Method invocation follows the R typestate
		System.out.print("Send travel destination request to Agent: ");
		String payload1 = safeRead(readerR);
		currentR.send_requestStringToA(payload1);
		int payload2 = currentR.receive_quoteintFromA();
		System.out.println("Received quote price from Agent: £" + payload2);
		System.out.print("Send quote price to Finance: £");
		int payload3 = Integer.parseInt(safeRead(readerR));
		currentR.send_checkintToF(payload3);
		switch(currentR.receive_Choice1LabelFromF()) {
			case APPROVE:
			System.out.println("Finance has approved the request");
			int payload4 = currentR.receive_approveintFromF();
			System.out.println("Received approve code from Finance: " + payload4);
			String payload5 = currentR.receive_ticketStringFromA();
			System.out.println("Received ticket from Agent: " + payload5);
			System.out.println("\n	----TRANSACTION COMPLETE----	");
			break;
			case REFUSE:
			System.out.println("Finance has refused the request");
			String payload6 = currentR.receive_refuseStringFromF();
			System.out.println("Received refusal from Finance: " + payload6);
			System.out.println("\n	----TRANSACTION COMPLETE----	");
			break;
		}
	}
}
