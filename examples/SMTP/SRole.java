package demos.SMTP;


import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.ServerSocket;


@Typestate("SProtocol")
public class SRole{
	private BufferedReader socketCIn = null;
	private PrintWriter socketCOut = null;
	public SRole() {
		// Bind the sockets
		//ServerSocketFactory ssf = ServerSocketFactory.getDefault();
		ServerSocket serverC = null;
		// Connecting to the server
		try {
			// Create the sockets
			//serverC = ssf.createServerSocket(20000);

			// The following is a standard server socket, comes from the translation
			serverC = new ServerSocket(20000);
		}
		catch(IOException e) {
			System.out.println("Unable to listen on ports");
			System.exit(-1);
		}
		// Accept a client connection
		Socket socketC = null;
		try {
			System.out.println("Accepting...");
			socketC = serverC.accept();
			System.out.println("C accepted");
		}
		catch (IOException e) {
			System.out.println("Accept failed");
			System.exit(-1);
		}
		// Create the read and write streams
		try {
			socketCIn = new BufferedReader(new InputStreamReader(socketC.getInputStream()));
			socketCOut = new PrintWriter(socketC.getOutputStream(), true);
		}
		catch (IOException e) {
			System.out.println("Read failed");
			System.exit(-1);
		}
	}
	public void send_220StringToC(String payload) {
		this.socketCOut.println(payload);
	}
	public Choice1 receive_Choice1LabelFromC() {
		String stringLabelChoice1 = "";
		try {
			stringLabelChoice1 = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error, unable to get label");
			System.exit(-1);
		}
		int intLabelChoice1 = Integer.parseInt(stringLabelChoice1);
		switch(intLabelChoice1) {
			case 1:
			return Choice1.EHLO;
			case 2:
			default:
			return Choice1.QUIT;
		}
	}
	public String receive_ehloStringFromC() {
		String line = "";
		try {
			line  = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error.");
			System.exit(-1);
		}
		return line;
	}
	public Choice2 send_Choice2LabelToC(String payload) {
		this.socketCOut.println(payload);
		int intLabelChoice2 = Integer.parseInt(payload);
		switch(intLabelChoice2) {
			case 1:
			return Choice2._250DASH;
			case 2:
			default:
			return Choice2._250;
		}
	}
	public void send_250dashStringToC(String payload) {
		this.socketCOut.println(payload);
	}
	public void send_250StringToC(String payload) {
		this.socketCOut.println(payload);
	}
	public Choice3 receive_Choice3LabelFromC() {
		String stringLabelChoice3 = "";
		try {
			stringLabelChoice3 = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error, unable to get label");
			System.exit(-1);
		}
		int intLabelChoice3 = Integer.parseInt(stringLabelChoice3);
		switch(intLabelChoice3) {
			case 1:
			return Choice3.STARTTLS;
			case 2:
			default:
			return Choice3.QUIT;
		}
	}
	public String receive_starttlsStringFromC() {
		String line = "";
		try {
			line  = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error.");
			System.exit(-1);
		}
		return line;
	}
	public Choice4 receive_Choice4LabelFromC() {
		String stringLabelChoice4 = "";
		try {
			stringLabelChoice4 = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error, unable to get label");
			System.exit(-1);
		}
		int intLabelChoice4 = Integer.parseInt(stringLabelChoice4);
		switch(intLabelChoice4) {
			case 1:
			return Choice4.AUTH;
			case 2:
			default:
			return Choice4.QUIT;
		}
	}
	public String receive_authStringFromC() {
		String line = "";
		try {
			line  = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error.");
			System.exit(-1);
		}
		return line;
	}
	public Choice5 send_Choice5LabelToC(String payload) {
		this.socketCOut.println(payload);
		int intLabelChoice5 = Integer.parseInt(payload);
		switch(intLabelChoice5) {
			case 1:
			return Choice5._235;
			case 2:
			default:
			return Choice5._535;
		}
	}
	public void send_235StringToC(String payload) {
		this.socketCOut.println(payload);
	}
	public Choice6 receive_Choice6LabelFromC() {
		String stringLabelChoice6 = "";
		try {
			stringLabelChoice6 = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error, unable to get label");
			System.exit(-1);
		}
		int intLabelChoice6 = Integer.parseInt(stringLabelChoice6);
		switch(intLabelChoice6) {
			case 1:
			return Choice6.MAIL;
			case 2:
			default:
			return Choice6.QUIT;
		}
	}
	public String receive_mailStringFromC() {
		String line = "";
		try {
			line  = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error.");
			System.exit(-1);
		}
		return line;
	}
	public Choice7 send_Choice7LabelToC(String payload) {
		this.socketCOut.println(payload);
		int intLabelChoice7 = Integer.parseInt(payload);
		switch(intLabelChoice7) {
			case 1:
			return Choice7._501;
			case 2:
			default:
			return Choice7._250;
		}
	}
	public void send_501StringToC(String payload) {
		this.socketCOut.println(payload);
	}
	public Choice8 receive_Choice8LabelFromC() {
		String stringLabelChoice8 = "";
		try {
			stringLabelChoice8 = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error, unable to get label");
			System.exit(-1);
		}
		int intLabelChoice8 = Integer.parseInt(stringLabelChoice8);
		switch(intLabelChoice8) {
			case 1:
			return Choice8.RCPT;
			case 2:
			default:
			return Choice8.DATA;
		}
	}
	public String receive_rcptStringFromC() {
		String line = "";
		try {
			line  = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error.");
			System.exit(-1);
		}
		return line;
	}
	public Choice9 send_Choice9LabelToC(String payload) {
		this.socketCOut.println(payload);
		int intLabelChoice9 = Integer.parseInt(payload);
		switch(intLabelChoice9) {
			case 1:
			default:
			return Choice9._250;
		}
	}
	public String receive_dataStringFromC() {
		String line = "";
		try {
			line  = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error.");
			System.exit(-1);
		}
		return line;
	}
	public void send_354StringToC(String payload) {
		this.socketCOut.println(payload);
	}
	public Choice10 receive_Choice10LabelFromC() {
		String stringLabelChoice10 = "";
		try {
			stringLabelChoice10 = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error, unable to get label");
			System.exit(-1);
		}
		int intLabelChoice10 = Integer.parseInt(stringLabelChoice10);
		switch(intLabelChoice10) {
			case 1:
			return Choice10.DATALINE;
			case 2:
			return Choice10.SUBJECT;
			case 3:
			default:
			return Choice10.ATAD;
		}
	}
	public String receive_datalineStringFromC() {
		String line = "";
		try {
			line  = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error.");
			System.exit(-1);
		}
		return line;
	}
	public String receive_subjectStringFromC() {
		String line = "";
		try {
			line  = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error.");
			System.exit(-1);
		}
		return line;
	}
	public String receive_atadStringFromC() {
		String line = "";
		try {
			line  = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error.");
			System.exit(-1);
		}
		return line;
	}
	public String receive_quitStringFromC() {
		String line = "";
		try {
			line  = this.socketCIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error.");
			System.exit(-1);
		}
		return line;
	}
	public void send_535StringToC(String payload) {
		this.socketCOut.println(payload);
	}
}
