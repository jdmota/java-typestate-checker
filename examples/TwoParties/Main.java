package examples.TwoParties;

class Main {
	public static void main(String [] args) {
		Thread t1 = new Thread(new BobRunner(9494));
		Thread t2 = new Thread(new AliceRunner(9494));

		t1.start();
		t2.start();
	}
}
