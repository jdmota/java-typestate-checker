package examples.Adder;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.ServerSocket;
import java.net.UnknownHostException;


public class SMain {
	public static String safeRead(BufferedReader readerS) {
		String readline = "";
		try {
			readline = readerS.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Output error, unable to read");
			System.exit(-1);
		}
		return readline;
	}
	public static void main(String[] args) {
		// Create the current role
		SRole currentS =  new SRole();
		// readerS can be used to input strings, and then use them in send method invocation
		BufferedReader readerS = new BufferedReader(new InputStreamReader(System.in));
		// Method invocation follows the S typestate
		_X: do{
				switch(currentS.receive_Choice1LabelFromC()) {
					case ADD:
					int payload1 = currentS.receive_AddintFromC();
					System.out.println("Received first int from C: " + payload1);
					int payload2 = currentS.receive_AddintFromC();
					System.out.println("Received secind int from C: " + payload2);
					int res = currentS.calculateResult(payload1, payload2); //add the 2 numbers
					System.out.println("Result of " + payload1 + " + " + payload2 + " = " + res);
					System.out.print("Send result to C: ");
					int payload3 = Integer.parseInt(safeRead(readerS));
					currentS.send_ResintToC(payload3);
					continue _X; //loop back to start of protocol (State0) until BYE is chosen
					case BYE:
					currentS.receive_ByeFromC();
					break _X;
				}
			} while(true);
		}
	}
