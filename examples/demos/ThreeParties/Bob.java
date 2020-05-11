package demos.ThreeParties;

//import mungo.lib.Typestate;

import java.io.IOException;
import java.net.ServerSocket;

@Typestate("BobProtocol")
class Bob{
	private SessionSocket alice;
	private SessionSocket carol;

	private int alicePort, carolPort;

	public Bob(int alicePort, int carolPort) {
		this.alicePort = alicePort;
		this.carolPort = carolPort;
	}

	void connect() {
		try {
			ServerSocket listener1 = new ServerSocket(alicePort);
			ServerSocket listener2 = new ServerSocket(carolPort);
			alice = new SessionSocket(listener1.accept());
			carol = new SessionSocket(listener2.accept());
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
	}

	void sendHelloToAlice(String s) {
		alice.send(s);
	}

	void sendHelloToCarol(String s) {
		carol.send(s);
	}

	void sendTimeChoiceToAlice() {
		alice.send(BobChoice.TIME);
		carol.send(BobChoice.END);
	}

	void sendTimeChoiceToCarol() {
		carol.send(BobChoice.TIME);
		alice.send(BobChoice.END);
	}

	int recvTimeFromAlice() {
		return alice.recvInt();
	}

	int recvTimeFromCarol() {
		return carol.recvInt();
	}

	void endCommunication() {
		alice.close();
		carol.close();
	}
}
