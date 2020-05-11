package demos.Traversal;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
@Typestate("BProtocol")
class BRole{
	SessionSocket a, c;

	BRole(int Aport, int Cport) {
		try {
			a = new SessionSocket(new Socket("localhost", Aport));
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}

		try {
			ServerSocket listener = new ServerSocket(Cport);
			c = new SessionSocket(listener.accept());
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
	}

	void DATAToA() {
		a.send(Choice.DATA);
	}

	void DATAToC() {
		c.send(Choice.DATA);
	}

	void NO_DToA() {
		a.send(Choice.NO_D);
	}

	void NO_DToC() {
		c.send(Choice.NO_D);
	}

	void ENDToA() {
		a.send(Choice.END);
	}

	void ENDToC() {
		c.send(Choice.END);
	}

	void nodeToA(Node n) {
		a.send(n);
	}

	void nodeToC(Node n) {
		c.send(n);
	}

	Node nodeFromA() {
		return (Node) a.receiveObject();
	}

	Node nodeFromC() {
		return (Node) c.receiveObject();
	}

	Choice choiceFromA() {
		return (Choice) a.receiveObject();
	}

	Choice choiceFromC() {
		return (Choice) c.receiveObject();
	}

}
