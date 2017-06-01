package examples.TwoParties;

import mungo.lib.Typestate;

import java.io.IOException;
import java.net.ServerSocket;


@Typestate("BobProtocol")
class Bob{
	private SessionSocket alice;
	private int port;

	public Bob(int port) {
		this.port = port;
	}

	void connect() {
		try {
			ServerSocket listener = new ServerSocket(port);
			alice = new SessionSocket(listener.accept());
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
	}

	void sendStringToAlice(String s) {
		alice.send(s);
	}

	void sendTimeChoiceToAlice() {
		alice.send(BobChoice.TIME);
	}

	void sendGreetingChoiceToAlice() {
		alice.send(BobChoice.GREET);
	}

	String recvGreetingFromAlice() {
		return alice.recvString();
	}

	int recvTimeFromAlice() {
		return alice.recvInt();
	}

	void endCommunication() {
		alice.close();
	}
}
