package demos.fibonacci;

import java.io.IOException;
import java.net.ServerSocket;
//import mungo.lib.Typestate;


@Typestate("NodeA")
class NodeARole{
	private SessionSocket s;

	NodeARole(int port) {
		try {
				ServerSocket listener = new ServerSocket(port);
				s = new SessionSocket(listener.accept());
		}
		catch(IOException e) {
				e.printStackTrace();
				System.exit(-1);
		}
	}

	void sendNEXTToB() {
		s.send(Choice.NEXT);
	}

	void sendENDToB() {
		s.send(Choice.END);
	}

	void sendLongToB(long a) {
		s.send(a);
	}

	long receiveLongFromB() {
		return s.receiveLong();
	}

}
