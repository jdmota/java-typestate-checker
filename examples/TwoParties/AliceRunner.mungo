package examples.TwoParties;

class AliceRunner implements Runnable {
	private int port;
	AliceRunner(int port) {
		this.port = port;
	}

	public void run() {
		Alice alice = new Alice(port);

		alice.connect();

		System.out.println("Alice received: " + alice.recvStringFromBob());

		switch(alice.choiceFromBob()){
			case TIME:
				System.out.println("Alice received: What is the time?");
				alice.sendTimeToBob(1900);
				break;

			case GREET:
				alice.sendGreetToBob("Hello Bob!");
				break;
		}
		alice.endCommunication();
	}
}
