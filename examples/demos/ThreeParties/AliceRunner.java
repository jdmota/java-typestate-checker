package demos.ThreeParties;

class AliceRunner implements Runnable {
	private int port;
	AliceRunner(int port) {
		this.port = port;
	}

	public void run() {
		Friend alice = new Friend(port);

		alice.connect();

		System.out.println("Alice received from Bob: " + alice.recvHelloFromBob());

		switch(alice.recvChoiceFromBob()) {
			case TIME:
				System.out.println("Alice received from Bob: What is the time?");
				alice.sendTimeToBob(1900);
				break;

			case END:
				break;
		}
		alice.endCommunication();
	}
}
