package examples.Adder;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.ServerSocket;
import java.net.UnknownHostException;
public class CMain {
	public static String safeRead(BufferedReader readerC) {
		String readline = "";
		try {
			readline = readerC.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error, unable to read");
			System.exit(-1);
		}
		return readline;
	}

	public static void main(String[] args) {
		// Create the current role
		CRole currentC =  new CRole();
		// readerC can be used to input strings, and then use them in send method invocation
		BufferedReader readerC = new BufferedReader(new InputStreamReader(System.in));
		// Method invocation follows the C typestate
		_X: do{
				System.out.print("Choose a label among [ADD, BYE]: ");
				int label1 = safeRead(readerC).matches("ADD") ? 1 : 2;
				switch(label1) {
					case 1 /*ADD*/:
					currentC.send_ADDToS();
					System.out.print("Send first int to S: ");
					int payload1 = Integer.parseInt(safeRead(readerC));
					currentC.send_AddintToS(payload1);
					System.out.print("Send second int to S: ");
					int payload2 = Integer.parseInt(safeRead(readerC));
					currentC.send_AddintToS(payload2);
					int payload3 = currentC.receive_ResintFromS();
					System.out.println("Received result from S: " + payload3);
					continue _X; //loop back to start of protocol (State0) until BYE is chosen
					case 2 /*BYE*/:
					currentC.send_BYEToS();
					currentC.send_ByeToS();
					break _X;
				}
			} while(true);
		}
	}
