package demos.POP3;


import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.Scanner;

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

		try {
			System.out.println("Starting SSL/POP3 test...\n");
			System.out.println("Creating socket connection.");

			CRole.sslSocket = (SSLSocket)CRole.sslSocketFactory.createSocket("pop.gmx.co.uk",995);
			CRole.sslIn = new BufferedReader(new InputStreamReader(CRole.sslSocket.getInputStream()));
			CRole.sslOut = new PrintWriter(CRole.sslSocket.getOutputStream(),true);

		// Create the current role
		CRole currentC =  new CRole();
		// readerC can be used to input strings, and then use them in send method invocation
		BufferedReader readerC = new BufferedReader(new InputStreamReader(System.in));
		// Method invocation follows the C typestate
		OKString payload1 = currentC.receive_OKNStringFromS();
		System.out.println("Received from S: " + payload1);
		_authentication_username: do{
			System.out.print("Choose a label among USER or QUIT: ");
			switch(safeRead(readerC)) {
				case "USER":
				currentC.send_USERToS();
				System.out.print("Send username to S: ");
				String payload2 = safeRead(readerC);
				currentC.send_USERStringToS(payload2);
				switch(currentC.receive_Choice1LabelFromS()) {
					case OK:
					OKString payload3 = currentC.receive_OKStringFromS();
					System.out.println("Received from S: " + payload3);
					_authentication_password: do{
						System.out.print("Choose a label among PASS or QUIT: ");
						switch(safeRead(readerC)) {
							case "PASS":
							currentC.send_PASSToS();
							System.out.print("Send password to S: ");
							String payload4 = safeRead(readerC);
							currentC.send_PASSStringToS(payload4);
							switch(currentC.receive_Choice1LabelFromS()) {
								case OK:
								OKString payload5 = currentC.receive_OKStringFromS();
								System.out.println("Received from S: " + payload5);
								_transaction: do{
									System.out.print("Choose a label among [STAT, LIST, LIST_N, RETR_N, DELE_N, RSET, TOP_N, NOOP, QUIT, UIDL, UIDL_N]: ");
									switch(safeRead(readerC)) {
									case "STAT":
									currentC.send_STATToS();
									Void payload6 = null;
									currentC.send_STATVoidToS(payload6);
									TwoInt payload7 = currentC.receive_OKNTwoIntFromS();
									System.out.println("Received from S: OK " + payload7);
									continue _transaction;
									case "LIST":
										currentC.send_LISTToS();
										Void payload8 = null;
										currentC.send_LISTVoidToS(payload8);
										switch(currentC.receive_Choice1LabelFromS()) {
											case OK:
											OKString payload9 = currentC.receive_OKStringFromS();
											System.out.println("Received from S: " + payload9);
											_summary_choice_list: do{
												switch(currentC.receive_Choice2LabelFromS()) {
													case DOT:
													Void payload10 = currentC.receive_DOTVoidFromS();
													System.out.println("Received from S: .");
													//System.out.println("Received from S: " + payload10);
													continue _transaction;
													//break summary_choice_list
													case SUM:
													SUMTwoInt payload11 = currentC.receive_SUMTwoIntFromS();
													System.out.println("Received from S: " + payload11);
													continue _summary_choice_list;
												}
											}
											while(true);
											//break _transaction;
											case ERR:
											ERRString payload12 = currentC.receive_ERRStringFromS();
											System.out.println("Received from S: " + payload12);
											continue _transaction;
										}
										continue _transaction;
									case "LIST_N":
										currentC.send_LIST_NToS();
										System.out.print("Send messagenumber to S: ");
										Scanner keyboard1 = new Scanner(System.in); //read keyboard
										int payload13 = keyboard1.nextInt(); //to declare payload13
										currentC.send_LIST_nIntToS(payload13);
										switch(currentC.receive_Choice1LabelFromS()) {
											case OK:
											TwoInt payload14 = currentC.receive_OKTwoIntFromS();
											System.out.println("Received from S: OK " + payload14);
											continue _transaction;
											case ERR:
											ERRString payload15 = currentC.receive_ERRStringFromS();
											System.out.println("Received from S: " + payload15);
											continue _transaction;
										}
										continue _transaction;
									case "RETR_N":
										currentC.send_RETR_NToS();
										System.out.print("Send messagenumber to S: ");
										Scanner keyboard2 = new Scanner(System.in); //read keyboard
										int payload16 = keyboard2.nextInt(); //to declare payload16
										currentC.send_RETR_nIntToS(payload16);
										switch(currentC.receive_Choice1LabelFromS()) {
											case OK:
											OKString payload17 = currentC.receive_OKStringFromS();
											System.out.println("Received from S: " + payload17);
											_summary_choice_retrieve: do{
												switch(currentC.receive_Choice2LabelFromS()) {
													case DOT:
													Void payload18 = currentC.receive_DOTVoidFromS();
													//System.out.println("Received from S: " + payload18);
													System.out.println("Received from S: .");
													//break _summary_choice_retrieve;
													continue _transaction;
													case SUM:
													SUMString payload19 = currentC.receive_SUMStringFromS();
													//System.out.println("Received from S: " + payload19);
													System.out.println(payload19);
													continue _summary_choice_retrieve;
												}
											}
											while(true);
											case ERR:
											ERRString payload20 = currentC.receive_ERRStringFromS();
											System.out.println("Received from S: " + payload20);
											continue _transaction;
										}
										continue _transaction;
									case "DELE_N":
										currentC.send_DELE_NToS();
										System.out.print("Send messagenumber to S: ");
										Scanner keyboard3 = new Scanner(System.in); //read keyboard
										int payload21 = keyboard3.nextInt(); //to declare payload21
										currentC.send_DELE_nIntToS(payload21);
										switch(currentC.receive_Choice1LabelFromS()) {
											case OK:
												OKString payload22 = currentC.receive_OKStringFromS();
												System.out.println("Received from S: " + payload22);
												continue _transaction;
											case ERR:
												ERRString payload23 = currentC.receive_ERRStringFromS();
												System.out.println("Received from S: " + payload23);
												continue _transaction;
										}
										continue _transaction;
									case "RSET":
										currentC.send_RSETToS();
										Void payload24 = null;
										currentC.send_RSETVoidToS(payload24);
										OKString payload25 = currentC.receive_OKNStringFromS();
										System.out.println("Received from S: " + payload25);
										continue _transaction;
									case "TOP_N":
										currentC.send_TOP_NToS();
										//System.out.print("Send messagenumber and number of lines to S: ");
										Scanner keyboard6 = new Scanner(System.in);
										System.out.print("Send messagenumber to S: ");
										int number1 = keyboard6.nextInt();
										System.out.print("Send number of lines to S: ");
										int number2 = keyboard6.nextInt();
										TwoInt payload26 = new TwoInt(number1, number2);
										//String payload26 = safeRead(readerC);
										currentC.send_TOP_nTwoIntToS(payload26);
										switch(currentC.receive_Choice1LabelFromS()) {
											case OK:
											OKString payload27 = currentC.receive_OKStringFromS();
											System.out.println("Received from S: " + payload27);
											_summary_choice_top: do{
												switch(currentC.receive_Choice2LabelFromS()) {
													case DOT:
														Void payload28 = currentC.receive_DOTVoidFromS();
														System.out.println("Received from S: .");
														//System.out.println("Received from S: " + payload28);
														//break _summary_choice_top;
														continue _transaction;
													case SUM:
														SUMString payload29 = currentC.receive_SUMStringFromS();
														System.out.println(/*"Received from S: " + */payload29);
														continue _summary_choice_top;
												}
											}
											while(true);
											case ERR:
												ERRString payload30 = currentC.receive_ERRStringFromS();
												System.out.println("Received from S: " + payload30);
												continue _transaction;
										}
										continue _transaction;
									case "NOOP":
										currentC.send_NOOPToS();
										Void payload31 = null;
										currentC.send_NOOPVoidToS(payload31);
										Void payload32 = currentC.receive_OKNVoidFromS();
										System.out.println("Received from S: " + payload32);
										continue _transaction;
									case "QUIT":
										currentC.send_QUITToS();
										Void payload33 = null;
										currentC.send_QUITVoidToS(payload33);
										OKString payload34 = currentC.receive_OKNStringFromS();
										System.out.println("Received from S: " + payload34);
										break _transaction;
									case "UIDL":
										currentC.send_UIDLToS();
										Void payload35 = null;
										currentC.send_UIDLVoidToS(payload35);
										switch(currentC.receive_Choice1LabelFromS()) {
											case OK:
											OKString payload36 = currentC.receive_OKStringFromS();
											System.out.println("Received from S: " + payload36);
											_summary_choice_uidl: do{
												switch(currentC.receive_Choice2LabelFromS()) {
													case DOT:
													Void payload37 = currentC.receive_DOTVoidFromS();
													System.out.println("Received from S: .");
													//System.out.println("Received from S: " + payload37);
													//break _summary_choice_uidl;
													continue _transaction;
													case SUM:
													SUMIntString payload38 = currentC.receive_SUMIntStringFromS();
													System.out.println("Received from S: " + payload38);
													continue _summary_choice_uidl;
												}
											}
											while(true);
											case ERR:
											ERRString payload39 = currentC.receive_ERRStringFromS();
											System.out.println("Received from S: " + payload39);
											continue _transaction;
										}
										continue _transaction;
									case "UIDL_N":
										currentC.send_UIDL_NToS();
										System.out.print("Send messagenumber to S: ");
										Scanner keyboard4 = new Scanner(System.in); //read keyboard
										int payload40 = keyboard4.nextInt(); //to declare payload40
										currentC.send_UIDL_nIntToS(payload40);
										switch(currentC.receive_Choice1LabelFromS()) {
											case OK:
											IntString payload41 = currentC.receive_OKIntStringFromS();
											System.out.println("Received from S: " + payload41);
											continue _transaction;
											case ERR:
											ERRString payload42 = currentC.receive_ERRStringFromS();
											System.out.println("Received from S: " + payload42);
											continue _transaction;
										}
										continue _transaction;
									}
								}
								while(true);
								break _authentication_password;
								case ERR:
									ERRString payload43 = currentC.receive_ERRStringFromS();
									System.out.println("Received from S: " + payload43);
									continue _authentication_password;
							}
							break _authentication_password;
							case "QUIT":
								currentC.send_QUITToS();
								Void payload44 = null;
								currentC.send_QUITVoidToS(payload44);
								OKString payload45 = currentC.receive_OKNStringFromS();
								System.out.println("Received from S: " + payload45);
								break _authentication_password;
						}
					}
					while(true);
					break _authentication_username;
					case ERR:
						ERRString payload46 = currentC.receive_ERRStringFromS();
						System.out.println("Received from S: " + payload46);
						continue _authentication_username;
				}
				break _authentication_username;
				case "QUIT":
					currentC.send_QUITToS();
					Void payload47 = null;
					currentC.send_QUITVoidToS(payload47);
					OKString payload48 = currentC.receive_OKNStringFromS();
					System.out.println("Received from S: " + payload48);
					break _authentication_username;
			}
		}
		while(true);

		CRole.sslIn.close();
		CRole.sslOut.close();

	} //end of try

	catch (IOException e) {
		System.out.println("Input/output error");
		System.exit(-1);
	}
} //end of main
} //end of class
