package demos.SMTP.FinalSMTP;

import sun.misc.BASE64Encoder;

import java.io.*;
import java.net.UnknownHostException;

public class CMain {
	static final String CRLF = "\\r\\n";

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
		SMTPMessage payload1 = SMTPMessage.Parse(currentC.receive_220StringFromS());
		System.out.println("Received from S: " + payload1);
		System.out.print("Choose a label among EHLO or QUIT: ");
		switch(safeRead(readerC)) {
			case "EHLO":
			currentC.send_EHLOToS();
			System.out.print("Send to S text for EHLO: ");
			String payload2 = safeRead(readerC);
			currentC.send_ehloStringToS((new SMTPMessage("EHLO", payload2)).toString());
			_X: do{
				switch(currentC.receive_Choice1LabelFromS()) {
					case _250DASH:
					String payload3 = currentC.receive_250dashStringFromS();
					continue _X;
					case _250:
					String payload4 = currentC.receive_250StringFromS();
					System.out.print("Choose a label among STARTTLS or QUIT: ");
					switch(safeRead(readerC)) {
						case "STARTTLS":
						currentC.send_STARTTLSToS();
						currentC.send_starttlsStringToS((new SMTPMessage("STARTTLS")).toString());
						SMTPMessage payload6 = SMTPMessage.Parse(currentC.receive_220StringFromS());
						
						try {
							currentC.sslSocket = (SSLSocket) ((SSLSocketFactory) SSLSocketFactory.getDefault()).createSocket(
																		currentC.socketS,
																		currentC.socketS.getInetAddress().getHostAddress(),
																		currentC.socketS.getPort(),
																		true);


							currentC.socketSIn = new BufferedReader(new InputStreamReader(currentC.sslSocket.getInputStream()));
							currentC.socketSOut = new PrintWriter(currentC.sslSocket.getOutputStream(), true);
						}
						catch(UnknownHostException e) {
							System.out.println("Unable to connect to the remote host");
							System.exit(-1);
						}
						catch (IOException e) {
							System.out.println("Input/output error");
							System.exit(-1);
						}
						
						System.out.println("Received from S: " + payload6);
						System.out.print("Choose a label among EHLO, or QUIT: ");
						int label3 = safeRead(readerC).equals("EHLO") ? 1 : 2;
						switch(label3) {
							case 1:
							currentC.send_EHLOToS();
							System.out.print("Send to S text for EHLO: ");
							String payload7 = safeRead(readerC);
							currentC.send_ehloStringToS((new SMTPMessage("EHLO", payload7)).toString());
							_X1: do{
								switch(currentC.receive_Choice1LabelFromS()) {
									case _250DASH:
									String payload8 = currentC.receive_250dashStringFromS();
									continue _X1;
									case _250:
									String payload9 = currentC.receive_250StringFromS();
									_Y: do{
										System.out.print("Choose a label among AUTH or QUIT: ");
										int label4 = safeRead(readerC).equals("AUTH") ? 1 : 2;
										switch(label4) {
											case 1:
											currentC.send_AUTHToS();
											System.out.print("Username: ");
											String username = safeRead(readerC);

											Console console = System.console();
											Object[] tmp = {};
											String password = new String(console.readPassword("Password: ", tmp));

											String token = "";
											try {
												BASE64Encoder encoder = new BASE64Encoder();
												token = encoder.encodeBuffer((username + "\0" + username + "\0" + password).getBytes("UTF-8")).trim();
											} catch (IOException e) {
												System.out.println("unable to use base64 encoding");
											}

											currentC.send_authStringToS((new SMTPMessage("AUTH PLAIN", token)).toString());
											
											switch(currentC.receive_Choice2LabelFromS()) {
												case _235:
												String payload11 = currentC.receive_235StringFromS();
												_Z1: do{
													System.out.print("Choose a label among MAIL or QUIT: ");
													int label5 = safeRead(readerC).equals("MAIL") ? 1 : 2;
													switch(label5) {
														case 1:
														currentC.send_MAILToS();
														System.out.print("Email from: ");
														String payload12 = safeRead(readerC);
														currentC.send_mailStringToS((new SMTPMessage("MAIL FROM:<"+payload12+">")).toString());
														
														switch(currentC.receive_Choice3LabelFromS()) {
															case _501:
															String payload13 = currentC.receive_501StringFromS();
															continue _Z1;
															case _250:
															String payload14 = currentC.receive_250StringFromS();
															System.out.println("Received from S: " + payload14);
															_Z2: do{
																System.out.print("Choose a label among RCPT or DATA: ");
																int label6 = safeRead(readerC).equals("RCPT") ? 1 : 2;
																switch(label6) {
																	case 1:
																	currentC.send_RCPTToS();
																	System.out.print("Send to S text for RCPT: ");
																	String payload15 = safeRead(readerC);
																	currentC.send_rcptStringToS((new SMTPMessage("RCPT TO:<"+payload15+">")).toString());
																	switch(currentC.receive_Choice4LabelFromS()) {
																		case _250:
																		String payload16 = currentC.receive_250StringFromS();
																		continue _Z2;
																	}
																	break _Z2;
																	case 2:
																	currentC.send_DATAToS();
																	currentC.send_dataStringToS((new SMTPMessage("DATA")).toString());
																	String payload18 = currentC.receive_354StringFromS();
																	System.out.println("Received from S: " + payload18);
																	_Z3: do{
																		System.out.print("Choose a label among DATALINE, SUBJECT or ATAD: ");
																		switch(safeRead(readerC)) {
																			case "DATALINE":
																			currentC.send_DATALINEToS();
																			System.out.print("Send to S text for DATALINE: ");
																			String payload19 = safeRead(readerC);
																			currentC.send_datalineStringToS(payload19 + CRLF);
																			continue _Z3;
																			case "SUBJECT":
																			currentC.send_SUBJECTToS();
																			System.out.print("Send to S text for SUBJECT: ");
																			String payload20 = safeRead(readerC);
																			currentC.send_subjectStringToS((new SMTPMessage("SUBJECT:"+payload20, CRLF)).toString());
																			continue _Z3;
																			case "ATAD":
																			currentC.send_ATADToS();
																			currentC.send_atadStringToS("." + CRLF);
																			String payload22 = currentC.receive_250StringFromS();
																			System.out.println("Received from S: " + payload22);
																			continue _Z1;
																		}
																	}
																	while(true);
																}
															}
															while(true);
															break _Z1;
														}
														break _Z1;
														case 2:
														currentC.send_QUITToS();
														String payload23 = "";
														currentC.send_quitStringToS(payload23);
														break _Z1;
													}
												}
												while(true);
												break _Y;
												case _535:
												String payload24 = currentC.receive_535StringFromS();
												//System.out.println("Received from S: error " + payload24);
												continue _Y;
											}
											break _Y;
											case 2:
											currentC.send_QUITToS();
											String payload25 = "";
											currentC.send_quitStringToS(payload25);
											break _Y;
										}
									}
									while(true);
									break _X1;
								}
							}
							while(true);
							break _X;
							case 2:
							currentC.send_QUITToS();
							String payload26 = "";
							currentC.send_quitStringToS(payload26);
							break _X;
						}
						break _X;
						case "QUIT":
						currentC.send_QUITToS();
						String payload27 = "";
						currentC.send_quitStringToS(payload27);
						break _X;
					}
					break _X;
				}
			}
			while(true);
			break;
			case "QUIT":
			currentC.send_QUITToS();
			String payload28 = "";
			currentC.send_quitStringToS(payload28);
			break;
		}
	}
}
