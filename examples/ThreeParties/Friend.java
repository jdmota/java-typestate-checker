package examples.ThreeParties;

import mungo.lib.Typestate;

import java.net.Socket;
import java.io.IOException;

@Typestate("FriendProtocol")
class Friend{
	private SessionSocket bob;
	private int port;

	public Friend(int port) {
		this.port = port;
	}

	void connect() {
		try {
			bob = new SessionSocket(new Socket("localhost", port));
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
	}

	String recvHelloFromBob() {
		return bob.recvString();
	}

	void sendTimeToBob(int i) {
		bob.send(i);
	}

	BobChoice recvChoiceFromBob() {
		return (BobChoice) bob.recvObject();
	}

	void endCommunication() {
		bob.close();
	}
}
