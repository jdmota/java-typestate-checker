package demos.ThreeParties;

class Main {
	public static void main(String [] args) {
		Thread t1 = new Thread(new BobRunner(9494, 9999));
		Thread t2 = new Thread(new AliceRunner(9494));
		Thread t3 = new Thread(new CarolRunner(9999));

		t1.start();
		t2.start();
		t3.start();
	}
}
