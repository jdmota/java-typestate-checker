package demos.Traversal;

import java.io.IOException;
import java.net.Socket;

@Typestate(value="CProtocol")
class CRole{
	SessionSocket a, b;

	CRole(int Aport, int Bport) {
		try {
			a = new SessionSocket(new Socket("localhost", Aport));
			b = new SessionSocket(new Socket("localhost", Bport));
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
	}

	void DATAToA() {
		a.send(Choice.DATA);
	}

	void DATAToB() {
		b.send(Choice.DATA);
	}

	void NO_DToA() {
		a.send(Choice.NO_D);
	}

	void NO_DToB() {
		b.send(Choice.NO_D);
	}

	void ENDToA() {
		a.send(Choice.END);
	}

	void ENDToB() {
		b.send(Choice.END);
	}

	void nodeToA(Node n) {
		a.send(n);
	}

	void nodeToB(Node n) {
		b.send(n);
	}

	Node nodeFromA() {
		return (Node) a.receiveObject();
	}

	Node nodeFromB() {
		return (Node) b.receiveObject();
	}

	Choice choiceFromA() {
		return (Choice) a.receiveObject();
	}

	Choice choiceFromB() {
		return (Choice) b.receiveObject();
	}

}
