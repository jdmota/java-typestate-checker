package examples.TwoParties;

class BobRunner implements Runnable {
	private int port;
	BobRunner(int port) {
		this.port = port;
	}

	public void run() {
		Bob bob = new Bob(port);

		bob.connect();

		bob.sendStringToAlice("Hello Alice!");

		if(true) {
			bob.sendTimeChoiceToAlice();
			System.out.println("Bob received: " + bob.recvTimeFromAlice());
		}
		else {
			bob.sendGreetingChoiceToAlice();
			System.out.println("Bob received the time: " + bob.recvGreetingFromAlice());
		}

		bob.endCommunication();
	}
}
