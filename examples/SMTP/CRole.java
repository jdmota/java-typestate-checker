package demos.SMTP;

import javax.net.ssl.SSLSocket;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.UnknownHostException;

@Typestate("CProtocol")
public class CRole {
	public BufferedReader socketSIn = null;
	public PrintWriter socketSOut = null;
	public Socket socketS = null;
	public SSLSocket sslSocket = null;

	public CRole() {
		try {
			//socketS = new Socket("smtp.gmail.com", 25);
			socketS = new Socket("smtp.gmail.com", 587);
			socketSIn = new BufferedReader(new InputStreamReader(socketS.getInputStream()));
			socketSOut = new PrintWriter(socketS.getOutputStream(), true);
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
	public String receive_220StringFromS() {
		String line = "";
		try {
			line  = this.socketSIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error.");
			System.exit(-1);
		}
		return line;
	}
	public Choice1 send_Choice1LabelToS(String payload) {
		//this.socketSOut.println(payload);
		int intLabelChoice1 = Integer.parseInt(payload);
		switch(intLabelChoice1) {
			case 1:
			return Choice1.EHLO;
			case 2:
			default:
			return Choice1.QUIT;
		}
	}
	public void send_ehloStringToS(String payload) {
		this.socketSOut.print(payload);
		this.socketSOut.flush();
	}
	public Choice2 receive_Choice2LabelFromS() {
		String stringLabelChoice2 = "";
		try {
			stringLabelChoice2 = this.socketSIn.readLine();
			System.out.println(stringLabelChoice2);
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error, unable to get label");
			System.exit(-1);
		}
		SMTPMessage message = SMTPMessage.Parse(stringLabelChoice2);
		int intLabelChoice2 = Integer.parseInt(message.getCommand());
		switch(intLabelChoice2) {
			case 250:
				if (message.getIsDashed()) {
					return Choice2._250DASH;
				} else {
					return Choice2._250;
				}
			default:
			return Choice2._250;
		}
	}
	public String receive_250dashStringFromS() {
		return "";
	}
	public String receive_250StringFromS() {
		return "";
	}
	public Choice3 send_Choice3LabelToS(String payload) {
		int intLabelChoice3 = Integer.parseInt(payload);
		switch(intLabelChoice3) {
			case 1:
			return Choice3.STARTTLS;
			case 2:
			default:
			return Choice3.QUIT;
		}
	}
	public void send_starttlsStringToS(String payload) {
		this.socketSOut.print(payload);
		this.socketSOut.flush();
	}
	public Choice4 send_Choice4LabelToS(String payload) {
		// this.socketSOut.println(payload);
		int intLabelChoice4 = Integer.parseInt(payload);
		switch(intLabelChoice4) {
			case 1:
			return Choice4.AUTH;
			case 2:
			default:
			return Choice4.QUIT;
		}
	}
	public void send_authStringToS(String payload) {
		this.socketSOut.print(payload);
		this.socketSOut.flush();
	}
	public Choice5 receive_Choice5LabelFromS() {
		String stringLabelChoice5 = "";
		try {
			stringLabelChoice5 = this.socketSIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error, unable to get label");
			System.exit(-1);
		}
		SMTPMessage message = SMTPMessage.Parse(stringLabelChoice5);
		int intLabelChoice5 = Integer.parseInt(message.getCommand());
		switch(intLabelChoice5) {
			case 235:
			return Choice5._235;
			case 535:
			default:
			return Choice5._535;
		}
	}
	public String receive_235StringFromS() {
		return "";
	}
	public Choice6 send_Choice6LabelToS(String payload) {
		// this.socketSOut.println(payload);
		int intLabelChoice6 = Integer.parseInt(payload);
		switch(intLabelChoice6) {
			case 1:
			return Choice6.MAIL;
			case 2:
			default:
			return Choice6.QUIT;
		}
	}
	public void send_mailStringToS(String payload) {
		this.socketSOut.print(payload);
		this.socketSOut.flush();
	}
	public Choice7 receive_Choice7LabelFromS() {
		String stringLabelChoice7 = "";
		try {
			stringLabelChoice7 = this.socketSIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error, unable to get label");
			System.exit(-1);
		}
		SMTPMessage message = SMTPMessage.Parse(stringLabelChoice7);
		int intLabelChoice7 = Integer.parseInt(message.getCommand());
		switch(intLabelChoice7) {
			case 501:
			return Choice7._501;
			case 250:
			default:
			return Choice7._250;
		}
	}
	public String receive_501StringFromS() {
		return "";
	}
	public Choice8 send_Choice8LabelToS(String payload) {
		// this.socketSOut.println(payload);
		int intLabelChoice8 = Integer.parseInt(payload);
		switch(intLabelChoice8) {
			case 1:
			return Choice8.RCPT;
			case 2:
			default:
			return Choice8.DATA;
		}
	}
	public void send_rcptStringToS(String payload) {
		this.socketSOut.print(payload);
		this.socketSOut.flush();
	}
	public Choice9 receive_Choice9LabelFromS() {
		String stringLabelChoice9 = "";
		try {
			stringLabelChoice9 = this.socketSIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error, unable to get label");
			System.exit(-1);
		}
		SMTPMessage message = SMTPMessage.Parse(stringLabelChoice9);
		int intLabelChoice9 = Integer.parseInt(message.getCommand());
		switch(intLabelChoice9) {
			case 250:
			default:
			return Choice9._250;
		}
	}
	public void send_dataStringToS(String payload) {
		this.socketSOut.print(payload);
		this.socketSOut.flush();
	}
	public String receive_354StringFromS() {
		String line = "";
		try {
			line  = this.socketSIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error.");
			System.exit(-1);
		}
		return line;
	}
	public Choice10 send_Choice10LabelToS(String payload) {
		// this.socketSOut.println(payload);
		int intLabelChoice10 = Integer.parseInt(payload);
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
	public void send_datalineStringToS(String payload) {
		this.socketSOut.print(payload);
		this.socketSOut.flush();
	}
	public void send_subjectStringToS(String payload) {
		this.socketSOut.print(payload);
		this.socketSOut.flush();
	}
	public void send_atadStringToS(String payload) {
		this.socketSOut.print(payload);
		this.socketSOut.flush();
	}
	public void send_quitStringToS(String payload) {
		this.socketSOut.print(payload);
		this.socketSOut.flush();
	}
	public String receive_535StringFromS() {
		return "";
	}
}
