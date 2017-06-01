package examples.TwoParties;

import java.io.*;
import java.net.Socket;

class SessionSocket {
	private Socket socket;

	private DataOutputStream out;
	private DataInputStream in;

	private PrintWriter outString;
	private BufferedReader inString;

	private ObjectOutputStream outObject;
	private ObjectInputStream inObject;

	public SessionSocket(Socket s) {
		try {
			socket = s;

			out = new DataOutputStream(socket.getOutputStream());
			in = new DataInputStream(socket.getInputStream());

			outString = new PrintWriter(socket.getOutputStream(), true);
			inString = new BufferedReader(new InputStreamReader(socket.getInputStream()));

			outObject = new ObjectOutputStream(socket.getOutputStream());
			inObject = new ObjectInputStream(socket.getInputStream());
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}

	}

	void close() {
		try {
			socket.close();
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}		
	}

	void send(int i) {
		try {
			out.writeInt(i);
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
	}

	void send(String s) {
		outString.println(s);
	}

	void send(Object o) {
		try {
			outObject.writeObject(o);
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
	}

	int recvInt() {
		int tmp = 0;
		try {
			tmp = in.readInt();
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
		return tmp;
	}

	String recvString() {
		String tmp = null;
		try {
			tmp = inString.readLine();
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
		return tmp;
	}

	Object recvObject() {
		Object tmp = null;
		try {
			tmp = inObject.readObject();
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
		catch(ClassNotFoundException e) {
			e.printStackTrace();
			System.exit(-1);
		}
		return tmp;
	}
}
