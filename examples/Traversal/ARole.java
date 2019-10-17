package demos.Traversal;

import java.net.ServerSocket;
import java.io.IOException;

@Typestate("AProtocol")
class ARole{
	SessionSocket b, c;

	ARole(int Bport, int Cport) {
		try {
			ServerSocket listener1 = new ServerSocket(Bport);
			ServerSocket listener2 = new ServerSocket(Cport);
			b = new SessionSocket(listener1.accept());
			c = new SessionSocket(listener2.accept());
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
	}

	void DATAToB() {
		b.send(Choice.DATA);
	}

	void DATAToC() {
		c.send(Choice.DATA);
	}

	void NO_DToB() {
		b.send(Choice.NO_D);
	}

	void NO_DToC() {
		c.send(Choice.NO_D);
	}

	void ENDToB() {
		b.send(Choice.END);
	}

	void ENDToC() {
		c.send(Choice.END);
	}

	void nodeToB(Node n) {
		b.send(n);
	}

	void nodeToC(Node n) {
		c.send(n);
	}

	Node nodeFromB() {
		return (Node) b.receiveObject();
	}

	Node nodeFromC() {
		return (Node) c.receiveObject();
	}

	Choice choiceFromB() {
		return (Choice) b.receiveObject();
	}

	Choice choiceFromC() {
		return (Choice) c.receiveObject();
	}

}
