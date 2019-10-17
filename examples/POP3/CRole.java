package examples.POP3;


import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.ServerSocket;
import java.net.UnknownHostException;

import javax.net.ssl.*;
import mungo.lib.Typestate;

@Typestate("CProtocol")
public class CRole {

	static SSLSocketFactory sslSocketFactory = (SSLSocketFactory)SSLSocketFactory.getDefault();
	static SSLSocket sslSocket;
	static BufferedReader sslIn;
	static PrintWriter sslOut;

	String currentmessage; //to store server messages in

	//reading server responses
	public String Servermessage() {
		try {
			this.currentmessage = this.sslIn.readLine();
			}
		catch(IOException e) {
			System.out.println("Input/Output error.");
			System.exit(-1);
			}
		return this.currentmessage;
	}
	public OKString receive_OKNStringFromS() {
		this.Servermessage();
		OKString okn;
		okn = OKString.Parse(this.currentmessage);
		return okn;
	}
	public void send_USERToS() {
		//this.socketSOut.println("USER");
	}
	public void send_QUITToS() {
		//this.socketSOut.println("QUIT");
	}
	public void send_USERStringToS(String payload) {
		this.sslOut.println("USER " + payload);
	}
	public Choice1 receive_Choice1LabelFromS() {
		this.Servermessage();
		if (this.currentmessage.toString().charAt(0) == '+') {
			return Choice1.OK;
			} else {
			return Choice1.ERR;
			}
	}
	public OKString receive_OKStringFromS() {
		OKString ok;
		ok = OKString.Parse(this.currentmessage);
		return ok;
	}
	public void send_PASSToS() {
		//this.socketSOut.println("PASS");
	}
	public void send_PASSStringToS(String payload) {
		this.sslOut.println("PASS " + payload);
	}
	public void send_STATToS() {
		//this.socketSOut.println("STAT");
	}
	public void send_LISTToS() {
		//this.socketSOut.println("LIST");
	}
	public void send_LIST_NToS() {
		//this.socketSOut.println("LIST_N");
	}
	public void send_RETR_NToS() {
		//this.socketSOut.println("RETR_N");
	}
	public void send_DELE_NToS() {
		//this.socketSOut.println("DELE_N");
	}
	public void send_RSETToS() {
		//this.socketSOut.println("RSET");
	}
	public void send_TOP_NToS() {
		//this.socketSOut.println("TOP_N");
	}
	public void send_NOOPToS() {
		//this.socketSOut.println("NOOP");
	}
	public void send_UIDLToS() {
		//this.socketSOut.println("UIDL");
	}
	public void send_UIDL_NToS() {
		//this.socketSOut.println("UIDL_N");
	}
	public void send_STATVoidToS(Void payload) {
		this.sslOut.println("STAT");
	}
	public TwoInt receive_OKNTwoIntFromS() {
		this.Servermessage();
		TwoInt zweiokn;
		zweiokn = TwoInt.Parse(this.currentmessage);
		return zweiokn;
	}
	public void send_LISTVoidToS(Void payload) {
		this.sslOut.println("LIST");
	}
	public Choice2 receive_Choice2LabelFromS() {
		this.Servermessage();
		if (this.currentmessage.toString().charAt(0) == '.') {
			return Choice2.DOT;
			} else {
			return Choice2.SUM;
			}
	}
	public Void receive_DOTVoidFromS() {
		return null;
	}
	public SUMTwoInt receive_SUMTwoIntFromS() {
		//sum is always part of choice
		SUMTwoInt sumzwei;
		sumzwei = SUMTwoInt.Parse(this.currentmessage);
		return sumzwei;
	}
	public ERRString receive_ERRStringFromS() {
		//always part of choice
		ERRString e;
		e = ERRString.Parse(this.currentmessage);
		return e;
	}
	public void send_LIST_nIntToS(int payload) {
		this.sslOut.println("LIST " + payload);
	}
	public TwoInt receive_OKTwoIntFromS() {
		//part of choice - do not update servermessage
		TwoInt zweiok;
		zweiok = TwoInt.Parse(this.currentmessage);
		return zweiok;
	}
	public void send_RETR_nIntToS(int payload) {
		this.sslOut.println("RETR " + payload);
	}
	public SUMString receive_SUMStringFromS() {
		//this.Servermessage(); - part of choice
		SUMString sum;
		sum = SUMString.Parse(this.currentmessage);
		return sum;
	}
	public void send_DELE_nIntToS(int payload) {
		this.sslOut.println("DELE " + payload);
	}
	public void send_RSETVoidToS(Void payload) {
		this.sslOut.println("RSET");
	}
	public void send_TOP_nTwoIntToS(TwoInt payload) {
		this.sslOut.println("TOP " + payload);
	}
	public void send_NOOPVoidToS(Void payload) {
		this.sslOut.println("NOOP");
	}
	public Void receive_OKNVoidFromS() {
		return null;
	}
	public void send_QUITVoidToS(Void payload) {
		this.sslOut.println("QUIT");
	}
	public void send_UIDLVoidToS(Void payload) {
		this.sslOut.println("UIDL");
	}
	public SUMIntString receive_SUMIntStringFromS() {
		//part of choice - do not call new servermessage
		SUMIntString sumIS;
		sumIS = SUMIntString.Parse(this.currentmessage);
		return sumIS;
	}
	public void send_UIDL_nIntToS(int payload) {
		this.sslOut.println("UIDL " + payload);
	}
	public IntString receive_OKIntStringFromS() {
		IntString is;
		is = IntString.Parse(this.currentmessage);
		return is;
	}
}
