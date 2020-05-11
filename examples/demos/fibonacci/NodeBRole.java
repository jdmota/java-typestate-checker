package demos.fibonacci;

import java.io.IOException;
import java.net.Socket;
//import mungo.lib.Typestate;


@Typestate("NodeB")
class NodeBRole {
	private SessionSocket s;

	NodeBRole(int port) {
		try {
			s = new SessionSocket(new Socket("localhost", port));
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
	}

	Choice receiveChoiceFromA() {
		return (Choice) s.receiveObject();
	}

	void sendLongToA(long a) {
		s.send(a);
	}

	long receiveLongFromA() {
		return s.receiveLong();
	}

}
