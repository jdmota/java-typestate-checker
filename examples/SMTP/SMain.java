package demos.SMTP;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

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
		System.out.print("Send to C: ");
		String payload1 = safeRead(readerS);
		currentS.send_220StringToC(payload1);
		switch(currentS.receive_Choice1LabelFromC()) {
			case EHLO:
			String payload2 = currentS.receive_ehloStringFromC();
			System.out.println("Received from C: " + payload2);
			_X: do{
				System.out.print("Choose a label among 250-, 250: ");
				String label1 = safeRead(readerS).equals("250-") ? "1" : "2";
				switch(currentS.send_Choice2LabelToC(label1)) {
					case _250DASH:
					System.out.print("Send to C: ");
					String payload3 = safeRead(readerS);
					currentS.send_250dashStringToC(payload3);
					continue _X;
					case _250:
					System.out.print("Send to C: ");
					String payload4 = safeRead(readerS);
					currentS.send_250StringToC(payload4);
					switch(currentS.receive_Choice3LabelFromC()) {
						case STARTTLS:
						String payload5 = currentS.receive_starttlsStringFromC();
						System.out.println("Received from C: " + payload5);
						System.out.print("Send to C: ");
						String payload6 = safeRead(readerS);
						currentS.send_220StringToC(payload6);
						switch(currentS.receive_Choice1LabelFromC()) {
							case EHLO:
							String payload7 = currentS.receive_ehloStringFromC();
							System.out.println("Received from C: " + payload7);
							_X1: do{
								System.out.print("Choose a label among 250-, 250: ");
								String label2 = safeRead(readerS).equals("250-") ? "1" : "2";
								switch(currentS.send_Choice2LabelToC(label2)) {
									case _250DASH:
									System.out.print("Send to C: ");
									String payload8 = safeRead(readerS);
									currentS.send_250dashStringToC(payload8);
									continue _X1;
									case _250:
									System.out.print("Send to C: ");
									String payload9 = safeRead(readerS);
									currentS.send_250StringToC(payload9);
									_Y: do{
										switch(currentS.receive_Choice4LabelFromC()) {
											case AUTH:
											String payload10 = currentS.receive_authStringFromC();
											System.out.println("Received from C: " + payload10);
											System.out.print("Choose a label among 235, 535: ");
											String label3 = safeRead(readerS).equals("235") ? "1" : "2";
											switch(currentS.send_Choice5LabelToC(label3)) {
												case _235:
												System.out.print("Send to C: ");
												String payload11 = safeRead(readerS);
												currentS.send_235StringToC(payload11);
												_Z1: do{
													switch(currentS.receive_Choice6LabelFromC()) {
														case MAIL:
														String payload12 = currentS.receive_mailStringFromC();
														System.out.println("Received from C: " + payload12);
														System.out.print("Choose a label among 501, 250: ");
														String label4 = safeRead(readerS).equals("501") ? "1" : "2";
														switch(currentS.send_Choice7LabelToC(label4)) {
															case _501:
															System.out.print("Send to C: ");
															String payload13 = safeRead(readerS);
															currentS.send_501StringToC(payload13);
															continue _Z1;
															case _250:
															System.out.print("Send to C: ");
															String payload14 = safeRead(readerS);
															currentS.send_250StringToC(payload14);
															_Z2: do{
																switch(currentS.receive_Choice8LabelFromC()) {
																	case RCPT:
																	String payload15 = currentS.receive_rcptStringFromC();
																	System.out.println("Received from C: " + payload15);
																	System.out.print("Choose a label among 250: ");
																	String label5 = safeRead(readerS).equals("250") ? "1" : "2";
																	switch(currentS.send_Choice9LabelToC(label5)) {
																		case _250:
																		System.out.print("Send to C: ");
																		String payload16 = safeRead(readerS);
																		currentS.send_250StringToC(payload16);
																		continue _Z2;
																	}
																	break _Z2;
																	case DATA:
																	String payload17 = currentS.receive_dataStringFromC();
																	System.out.println("Received from C: " + payload17);
																	System.out.print("Send to C: ");
																	String payload18 = safeRead(readerS);
																	currentS.send_354StringToC(payload18);
																	_Z3: do{
																		switch(currentS.receive_Choice10LabelFromC()) {
																			case DATALINE:
																			String payload19 = currentS.receive_datalineStringFromC();
																			System.out.println("Received from C: " + payload19);
																			continue _Z3;
																			case SUBJECT:
																			String payload20 = currentS.receive_subjectStringFromC();
																			System.out.println("Received from C: " + payload20);
																			continue _Z3;
																			case ATAD:
																			String payload21 = currentS.receive_atadStringFromC();
																			System.out.println("Received from C: " + payload21);
																			System.out.print("Send to C:");
																			String payload22 = safeRead(readerS);
																			currentS.send_250StringToC(payload22);
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
														String payload23 = currentS.receive_quitStringFromC();
														System.out.println("Received from C: " + payload23);
														break _Z1;
													}
												}
												while(true);
												break _Y;
												case _535:
												System.out.print("Send to C: ");
												String payload24 = safeRead(readerS);
												currentS.send_535StringToC(payload24);
												continue _Y;
											}
											break _Y;
											case QUIT:
											String payload25 = currentS.receive_quitStringFromC();
											System.out.println("Received from C: " + payload25);
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
							String payload26 = currentS.receive_quitStringFromC();
							System.out.println("Received from C: " + payload26);
							break _X;
						}
						break _X;
						case QUIT:
						String payload27 = currentS.receive_quitStringFromC();
						System.out.println("Received from C: " + payload27);
						break _X;
					}
					break _X;
				}
			}
			while(true);
			break;
			case QUIT:
			String payload28 = currentS.receive_quitStringFromC();
			System.out.println("Received from C: " + payload28);
			break;
		}
	}
}
