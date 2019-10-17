package demos.file_example;
import java.io.*;

class MyBufferedReader {
	private BufferedReader reader;
	private String file;

	MyBufferedReader(String file) {
		this.file = file;
	}

	boolean open() {
		try {
			reader = new BufferedReader(new FileReader(file));
		}
		catch(FileNotFoundException e) {
			return false;
		}
		return true;
	}

	void close() {
		try {
			reader.close();
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
	}

	boolean ready() {
		try {
			if(reader.ready())
				return true;
		}
		catch(IOException e) {
			return false;
		}
		return false;
	}

	char read() {
		int c = -1;
		try {
			c = reader.read();
		}
		catch(IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
		return (char) c;
	}
}
