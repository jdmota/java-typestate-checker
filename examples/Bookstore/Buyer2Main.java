package examples.Bookstore;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.ServerSocket;
import java.net.UnknownHostException;


public class Buyer2Main {
	public static String safeRead(BufferedReader readerBuyer2) {
		String readline = "";
		try {
			readline = readerBuyer2.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error, unable to read");
			System.exit(-1);
		}
		return readline;
	}
	public static void main(String[] args) {
		// Create the current role
		Buyer2Role currentBuyer2 =  new Buyer2Role();
		// readerBuyer2 can be used to input strings, and then use them in send method invocation
		BufferedReader readerBuyer2 = new BufferedReader(new InputStreamReader(System.in));
		// Method invocation follows the Buyer2 typestate
		int payload1 = currentBuyer2.receive_quoteintFromBuyer1();
		System.out.println("Received book price quote from Buyer1: £" + payload1);
		System.out.print("Choose a label among [AGREE, QUIT]: ");
		int label1 = safeRead(readerBuyer2).matches("AGREE") ? 1 : 2;
		switch(label1) {
			case 1 /*AGREE*/:
			currentBuyer2.send_AGREEToBuyer1();
			System.out.print("Send agreement message to Buyer1: ");
			String payload2 = safeRead(readerBuyer2);
			currentBuyer2.send_agreeStringToBuyer1(payload2);
			System.out.print("Send agreement message to Seller: ");
			String payload3 = safeRead(readerBuyer2);
			currentBuyer2.send_agreeStringToSeller(payload3);
			//currentBuyer2.receive_OKFromSeller();
			System.out.print("Send transfer to Seller: £");
			int payload4 = Integer.parseInt(safeRead(readerBuyer2));
			currentBuyer2.send_transferintToSeller(payload4);
			System.out.println("\n---Transaction complete: book sold---");
			break;
			case 2 /*QUIT*/:
			currentBuyer2.send_QUITToBuyer1();
			System.out.print("Send quit message to Buyer1: ");
			String payload5 = safeRead(readerBuyer2);
			currentBuyer2.send_quitStringToBuyer1(payload5);
			System.out.print("Send quit message to Seller: ");
			String payload6 = safeRead(readerBuyer2);
			currentBuyer2.send_quitStringToSeller(payload6);
			System.out.println("\n---Transaction complete: no sale---");
			break;
		}
	}
}
