package examples.fibonacci;


class NodeB implements Runnable {
	private int port;

	NodeB(int port) {
		this.port = port;
	}

	public void run() {
		NodeBRole a = new NodeBRole(port);

		long x = 1;

		loop: do {
			switch(a.receiveChoiceFromA()) {
				case NEXT:
					x += a.receiveLongFromA();
					a.sendLongToA(x);
					continue loop;
				case END:
					break loop;
			}
		} while(true);
	}
}
