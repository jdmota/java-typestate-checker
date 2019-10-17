package demos.SMTP;

import sun.misc.BASE64Encoder;

import javax.net.ssl.SSLSocket;
import javax.net.ssl.SSLSocketFactory;
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
	public static void main(String args[]) {
		// Create the current role
		CRole currentC =  new CRole();
		// readerC can be used to input strings, and then use them in send method invocation
		BufferedReader readerC = new BufferedReader(new InputStreamReader(System.in));

		// Method invocation follows the C typestate
		SMTPMessage payload1 = SMTPMessage.Parse(currentC.receive_220StringFromS());
		System.out.println("Received from S: " + payload1);
		System.out.print("Choose a label among EHLO, or QUIT: ");
		String label1 = safeRead(readerC).equals("EHLO") ? "1" : "2";
		switch(currentC.send_Choice1LabelToS(label1)) {
			case EHLO:
			System.out.print("Send to S text for EHLO: ");
			String payload2 = safeRead(readerC);
			currentC.send_ehloStringToS((new SMTPMessage("EHLO", payload2)).toString());
			_X: do{
				switch(currentC.receive_Choice2LabelFromS()) {
					case _250DASH:
					String payload3 = currentC.receive_250dashStringFromS();
					// System.out.println("Received from S: " + payload3);
					continue _X;

					case _250:
					String payload4 = currentC.receive_250StringFromS();
					// System.out.println("Received from S: " + payload4);
					System.out.print("Choose a label among STARTTLS, or QUIT: ");
					String label2 = safeRead(readerC).equals("STARTTLS") ? "1" : "2";

					switch(currentC.send_Choice3LabelToS(label2)) {
						case STARTTLS:
						// System.out.print("Send to S text for STARTTLS: ");
						// String payload5 = safeRead(readerC);
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
						String label3 = safeRead(readerC).equals("EHLO") ? "1" : "2";

						switch(currentC.send_Choice1LabelToS(label3)) {
							case EHLO:
							System.out.print("Send to S text for EHLO: ");
							String payload7 = safeRead(readerC);
							currentC.send_ehloStringToS((new SMTPMessage("EHLO", payload7)).toString());
							_X1: do{
								switch(currentC.receive_Choice2LabelFromS()) {
									case _250DASH:
									String payload8 = currentC.receive_250dashStringFromS();
									// System.out.println("Received from S: " + payload8);
									continue _X1;

									case _250:
									String payload9 = currentC.receive_250StringFromS();
									// System.out.println("Received from S: " + payload9);
									_Y: do{
										System.out.print("Choose a label among AUTH, QUIT: ");
										String label4 = safeRead(readerC).equals("AUTH") ? "1" : "2";
										switch(currentC.send_Choice4LabelToS(label4)) {
											case AUTH:
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

											switch(currentC.receive_Choice5LabelFromS()) {
												case _235:
												String payload11 = currentC.receive_235StringFromS();
												// System.out.println("Received from S: " + payload11);
												_Z1: do{
													System.out.print("Choose a label among MAIL, or QUIT: ");
													String label5 = safeRead(readerC).equals("MAIL") ? "1" : "2";
													switch(currentC.send_Choice6LabelToS(label5)) {
														case MAIL:
														System.out.print("Email from: ");
														String payload12 = safeRead(readerC);
														currentC.send_mailStringToS((new SMTPMessage("MAIL FROM:<"+payload12+">")).toString());

														switch(currentC.receive_Choice7LabelFromS()) {
															case _501:
															String payload13 = currentC.receive_501StringFromS();
															// System.out.println("Received from S: " + payload13);
															continue _Z1;

															case _250:
															String payload14 = currentC.receive_250StringFromS();
															System.out.println("Received from S: " + payload14);
															_Z2: do{
																System.out.print("Choose a label among RCPT, or DATA: ");
																String label6 = safeRead(readerC).equals("RCPT") ? "1" : "2";
																switch(currentC.send_Choice8LabelToS(label6)) {
																	case RCPT:
																	System.out.print("Send to S text for RCPT: ");
																	String payload15 = safeRead(readerC);
																	currentC.send_rcptStringToS((new SMTPMessage("RCPT TO:<"+payload15+">")).toString());
																	switch(currentC.receive_Choice9LabelFromS()) {
																		case _250:
																		String payload16 = currentC.receive_250StringFromS();
																		// System.out.println("Received from S: " + payload16);
																		continue _Z2;
																	}
																	break _Z2;
																	case DATA:
																	// System.out.print("Send to S text for DATA: ");
																	// String payload17 = safeRead(readerC);
																	currentC.send_dataStringToS((new SMTPMessage("DATA")).toString());
																	String payload18 = currentC.receive_354StringFromS();
																	System.out.println("Received from S: " + payload18);
																	_Z3: do{
																		String label7 = "";
																		System.out.print("Choose a label among DATALINE, SUBJECT, or ATAD: ");
																		String sR = safeRead(readerC);
																		if (sR.equals("DATALINE")) {
																			label7 = "1";
																		} else if (sR.equals("SUBJECT")) {
																			label7 = "2";
																		} else {
																			label7 = "3";
																		}
																		switch(currentC.send_Choice10LabelToS(label7)) {
																			case DATALINE:
																			System.out.print("Send to S text for DATALINE: ");
																			String payload19 = safeRead(readerC);
																			currentC.send_datalineStringToS(payload19 + CRLF);
																			continue _Z3;
																			case SUBJECT:
																			System.out.print("Send to S text for SUBJECT: ");
																			String payload20 = safeRead(readerC);
																			currentC.send_subjectStringToS((new SMTPMessage("SUBJECT:"+payload20, CRLF)).toString());
																			continue _Z3;
																			case ATAD:
																			// System.out.print("Send to S text for ATAD: ");
																			// String payload21 = safeRead(readerC);
																			currentC.send_atadStringToS("." + CRLF);
																			String payload22 = currentC.receive_250StringFromS();
																			System.out.println("Received from S: " + payload22);
																			continue _Z1;
																		}
																	}
																	while(true);
																	//break _Z2;
																}
															}
															while(true);
															break _Z1;
														}
														break _Z1;
														case QUIT:
														//System.out.print("Send to S text for QUIT: ");
														String payload23 = "";
														currentC.send_quitStringToS(payload23);
														break _Z1;
													}
												}
												while(true);
												break _Y;
												case _535:
												String payload24 = currentC.receive_535StringFromS();
												System.out.println("Received from S: " + payload24);
												continue _Y;
											}
											break _Y;
											case QUIT:
											//System.out.print("Send to S text for QUIT: ");
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
							case QUIT:
							//System.out.print("Send to S text for QUIT: ");
							String payload26 = "";
							currentC.send_quitStringToS(payload26);
							break _X;
						}
						break _X;
						case QUIT:
						//System.out.print("Send to S text for QUIT: ");
						String payload27 = "";
						currentC.send_quitStringToS(payload27);
						break _X;
					}
					break _X;
				}
			}
			while(true);
			break;
			case QUIT:
			//System.out.print("Send to S text for QUIT: ");
			String payload28 = "";
			currentC.send_quitStringToS(payload28);
			break;
		}
	}
}
