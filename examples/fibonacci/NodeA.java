package examples.fibonacci;

class NodeA implements Runnable {
	private int port;
	private int index;

	NodeA(int port, int index) {
		this.port = port;
		this.index = index;
	}

	public void run() {
		NodeARole b = new NodeARole(port);

		long x = 0;

		for(int i = 0; i < index; i++) {
			b.sendNEXTToB();
			b.sendLongToB(x);
			if (++i < index)
				x += b.receiveLongFromB();
			else
				x = b.receiveLongFromB();
		}
		b.sendENDToB();

		System.out.println("The " + index + " fibonacci number is: " + x);
	}
}
