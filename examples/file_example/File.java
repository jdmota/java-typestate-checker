package demos.file_example;

@Typestate("FileProtocol")
class File {
	protected MyBufferedReader reader;
	private String file;
	private char[] readBuffer;
	private int i;

	File(String file) {
		this.file = file;
		reader = new MyBufferedReader(file);
		readBuffer = new char[1024];
		i = 0;
	}

	Status open() {
		if(reader.open())
			return Status.OK;
		return Status.ERROR;
	}

	void close() {
		reader.close();
	}

	BooleanEnum hasNext() {
		if(reader.ready())
			return BooleanEnum.TRUE;
		return BooleanEnum.FALSE;
	}

	void read() {
		readBuffer[i++] = reader.read();
	}

	//The next two methods demonstrate that
	// a created typestate object can
	// be assigned in a linear way and
	// passed around as an argument

	public static void main(String[] args) {
		File myFile = new File("file.txt");
		File a = myFile;
		processFile(a);
	}

	public static void processFile(File myFile) {
		switch(myFile.open()) {
			case OK:
				if(true) {
					loop:
					while(true) {
						switch(myFile.hasNext()) {
							case TRUE:
								myFile.read();
								break;
							case FALSE:
								break loop;
						}

					}
				}
				myFile.close();
				break;
			case ERROR:
				System.out.println("File <file.txt> not found!");
				break;
		}
	}

}
