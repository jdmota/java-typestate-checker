package demos.ThreeParties;

class CarolRunner implements Runnable {
	private int port;
	CarolRunner(int port) {
		this.port = port;
	}

	public void run() {
		Friend carol = new Friend(port);

		carol.connect();

		System.out.println("Carol received from Bob: " + carol.recvHelloFromBob());
		switch(carol.recvChoiceFromBob()) {
			case TIME:
				System.out.println("Carol received from Bob: What is the time?");
				carol.sendTimeToBob(1500);
				break;

			case END:
				break;
		}
		carol.endCommunication();
	}
}
