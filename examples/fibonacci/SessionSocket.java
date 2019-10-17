package examples.fibonacci;

import java.net.ServerSocket;
import java.net.Socket;

import java.io.IOException;
import java.lang.ClassNotFoundException;

import java.io.DataOutputStream;
import java.io.DataInputStream;

import java.io.PrintWriter;

import java.io.BufferedReader;
import java.io.InputStreamReader;

import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;


class SessionSocket {
	private Socket socket;

	private DataOutputStream outData;
	private DataInputStream inData;

	private PrintWriter outString;
	private BufferedReader inString;

	private ObjectOutputStream outObject;
	private ObjectInputStream inObject;

	public SessionSocket(Socket s) {
		try {
			socket = s;

			outData = new DataOutputStream(socket.getOutputStream());
			inData = new DataInputStream(socket.getInputStream());

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

	void send(long i) {
		try {
			outData.writeLong(i);
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
	}

	void send(int i) {
		try {
			outData.writeInt(i);
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

	long receiveLong() {
		long tmp = 0;
		try {
			tmp = inData.readLong();
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
		return tmp;
	}

	int receiveInt() {
		int tmp = 0;
		try {
			tmp = inData.readInt();
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
		return tmp;
	}

	String receiveString() {
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

	Object receiveObject() {
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
