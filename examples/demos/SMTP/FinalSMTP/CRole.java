package demos.SMTP.FinalSMTP;

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

	// Typestate method definitions
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
	public void send_EHLOToS() {
		// This method corresponds to selecting the command EHLO,
		// hence its body is empty.
	}
	public void send_QUITToS() {
		// This method corresponds to selecting the command QUIT,
		// hence its body is empty.
	}
	public void send_ehloStringToS(String payload) {
		this.socketSOut.print(payload);
		this.socketSOut.flush();
	}
	public Choice1 receive_Choice1LabelFromS()  {
		String stringLabelChoice1 = "";
		try {
			stringLabelChoice1 = this.socketSIn.readLine();
			System.out.println(stringLabelChoice1);
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error, unable to get label");
			System.exit(-1);
		}
		SMTPMessage message = SMTPMessage.Parse(stringLabelChoice1);
		int intLabelChoice1 = Integer.parseInt(message.getCommand());
		switch(intLabelChoice1) {
			case 250:
				if (message.getIsDashed()) {
					return Choice1._250DASH;
				} else {
					return Choice1._250;
				}
			default:
			return Choice1._250;
		}
	}
	public String receive_250dashStringFromS() {
		return "";
	}
	public String receive_250StringFromS() {
		return "";
	}
	public void send_STARTTLSToS() {
		// This method corresponds to selecting the command STARTTLS,
		// hence its body is empty.
	}
	public void send_starttlsStringToS(String payload) {
		this.socketSOut.print(payload);
		this.socketSOut.flush();
	}
	public void send_AUTHToS() {
		// This method corresponds to selecting the command AUTH,
		// hence its body is empty.
	}
	public void send_authStringToS(String payload) {
		this.socketSOut.print(payload);
		this.socketSOut.flush();
	}
	public Choice2 receive_Choice2LabelFromS() {
		String stringLabelChoice2 = "";
		try {
			stringLabelChoice2 = this.socketSIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error, unable to get label");
			System.exit(-1);
		}
		SMTPMessage message = SMTPMessage.Parse(stringLabelChoice2);
		int intLabelChoice2 = Integer.parseInt(message.getCommand());
		switch(intLabelChoice2) {
			case 235:
			return Choice2._235;
			case 535:
			default:
			return Choice2._535;
		}
	}
	public String receive_235StringFromS() {
		return "";
	}
	public void send_MAILToS() {
		// This method corresponds to selecting the command MAIL,
		// hence its body is empty.
	}
	public void send_mailStringToS(String payload) {
		this.socketSOut.print(payload);
		this.socketSOut.flush();
	}
	public Choice3 receive_Choice3LabelFromS() {
		String stringLabelChoice3 = "";
		try {
			stringLabelChoice3 = this.socketSIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error, unable to get label");
			System.exit(-1);
		}
		SMTPMessage message = SMTPMessage.Parse(stringLabelChoice3);
		int intLabelChoice3 = Integer.parseInt(message.getCommand());
		switch(intLabelChoice3) {
			case 501:
			return Choice3._501;
			case 250:
			default:
			return Choice3._250;
		}
	}
	public String receive_501StringFromS() {
		return "";
	}
	public void send_RCPTToS() {
		// This method corresponds to selecting the command RCPT,
		// hence its body is empty.
	}
	public void send_DATAToS() {
		// This method corresponds to selecting the command DATA,
		// hence its body is empty.
	}
	public void send_rcptStringToS(String payload) {
		this.socketSOut.print(payload);
		this.socketSOut.flush();
	}
	public Choice4 receive_Choice4LabelFromS()  {
		String stringLabelChoice4 = "";
		try {
			stringLabelChoice4 = this.socketSIn.readLine();
		}
		catch(IOException e) {
			System.out.println("Input/Outpur error, unable to get label");
			System.exit(-1);
		}
		SMTPMessage message = SMTPMessage.Parse(stringLabelChoice4);
		int intLabelChoice4 = Integer.parseInt(message.getCommand());
		switch(intLabelChoice4) {
			case 250:
			default:
			return Choice4._250;
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
	public void send_DATALINEToS() {
		// This method corresponds to selecting the command DATALINE,
		// hence its body is empty.
	}
	public void send_SUBJECTToS() {
		// This method corresponds to selecting the command SUBJECT,
		// hence its body is empty.
	}
	public void send_ATADToS() {
		// This method corresponds to selecting the command ATAD,
		// hence its body is empty.
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
