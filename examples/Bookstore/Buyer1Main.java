package examples.Bookstore;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.ServerSocket;
import java.net.UnknownHostException;


public class Buyer1Main {
	public static String safeRead(BufferedReader readerBuyer1) {
		String readline = "";
		try {
			readline = readerBuyer1.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error, unable to read");
			System.exit(-1);
		}
		return readline;
	}
	public static void main(String[] args) {
		// Create the current role
		Buyer1Role currentBuyer1 =  new Buyer1Role();
		// readerBuyer1 can be used to input strings, and then use them in send method invocation
		BufferedReader readerBuyer1 = new BufferedReader(new InputStreamReader(System.in));
		// Method invocation follows the Buyer1 typestate
		System.out.print("Send book title to Seller: ");
		String payload1 = safeRead(readerBuyer1);
		currentBuyer1.send_bookStringToSeller(payload1);
		int payload2 = currentBuyer1.receive_bookintFromSeller();
		System.out.println("Received book price from Seller: £" + payload2);
		System.out.print("Send book price quote to Buyer2: £");
		int payload3 = Integer.parseInt(safeRead(readerBuyer1));
		currentBuyer1.send_quoteintToBuyer2(payload3);
		switch(currentBuyer1.receive_Choice1LabelFromBuyer2()) {
			case AGREE:
			String payload4 = currentBuyer1.receive_agreeStringFromBuyer2();
			System.out.println("Received agreement message from Buyer2: " + payload4);
			System.out.print("Send transfer to Seller: £");
			int payload5 = Integer.parseInt(safeRead(readerBuyer1));
			currentBuyer1.send_transferintToSeller(payload5);
			System.out.println("\n---Transaction complete: book purchased---");
			break;
			case QUIT:
			String payload6 = currentBuyer1.receive_quitStringFromBuyer2();
			System.out.println("Received quit message from Buyer2: " + payload6);
			System.out.println("\n---Transaction complete: no sale---");
			break;
		}
	}
}
