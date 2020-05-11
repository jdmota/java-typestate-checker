package demos.ThreeParties;

class BobRunner implements Runnable {
	private int alicePort;
	private int carolPort;
	BobRunner(int alicePort, int carolPort) {
		this.alicePort = alicePort;
		this.carolPort = carolPort;
	}

	public void run() {
		Bob bob = new Bob(alicePort, carolPort);

		bob.connect();

		bob.sendHelloToAlice("Hello Alice!");
		bob.sendHelloToCarol("Hello Carol!");

		bob.sendTimeChoiceToCarol();
		System.out.println("Bob received the time from Carol: " + bob.recvTimeFromCarol());

		bob.endCommunication();
	}
}
