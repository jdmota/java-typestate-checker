package demos.Traversal;

class B implements Runnable {
	int Aport, Cport;

	B(int Aport, int Cport) {
		this.Aport = Aport;
		this.Cport = Cport;
	}

	public void run() {
		Node node = null;
		BRole b = new BRole(Aport, Cport);

		Node queue[] = new Node[100];
		int head = 0; int tail = 0;

		loop: do {
			switch(b.choiceFromA()) {
				case DATA:
					queue[head++] = b.nodeFromA(); //put in the queue
					break;
				case NO_D:
					break;
				case END:
					break loop;
			}

			// get from queue
			if(queue[tail] != null) {
				node = queue[tail++];
				System.out.println("B: " + node.get());
			}
			else {
				node = null;
			}

			if(node != null && node.left() != null) {
				b.DATAToA(); b.nodeToA(node.left());
			}
			else if (node !=null && node.right() != null) {
				b.NO_DToA();
			}
			else {
				b.ENDToA();
			}

			if(node != null && node.right() != null) {
				b.DATAToC(); b.nodeToC(node.right());
			}
			else {
				b.NO_DToC();
			}

			switch(b.choiceFromC()) {
				case DATA:
					queue[head++] = b.nodeFromC(); //put in the queue
					break;
				case NO_D:
					break;
				case END:
					//set a flag
					break;
			}
			continue loop;
		} while(true);
	}
}
