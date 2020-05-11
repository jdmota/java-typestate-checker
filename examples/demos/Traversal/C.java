package demos.Traversal;

class C implements Runnable {
	int Aport, Bport;

	C(int Aport, int Bport) {
		this.Aport = Aport;
		this.Bport = Bport;
	}

	public void run() {
		Node node = null;
		CRole c = new CRole(Aport, Bport);

		Node queue[] = new Node[100];
		int head = 0; int tail = 0;

		loop: do {
			switch(c.choiceFromA()) {
				case DATA:
					queue[head++] = c.nodeFromA(); //put in the queue
					break;
				case NO_D:
					break;
				case END:
					break loop;
			}

			switch(c.choiceFromB()) {
				case DATA:
					queue[head++] = c.nodeFromB(); //put in the queue
					break;
				case NO_D:
					break;
				case END:
					//set a flag
					break;
			}

			// get from queue
			if(queue[tail] != null) {
				node = queue[tail++];
				System.out.println("C: " + node.get());
			}
			else {
				node = null;
			}

			if(node != null && node.left() != null) {
				c.DATAToA(); c.nodeToA(node.left());
			}
			else if (node !=null && node.right() != null) {
				c.NO_DToA();
			}
			else {
				c.ENDToA();
			}

			if(node != null && node.right() != null) {
				c.DATAToB(); c.nodeToB(node.right());
			}
			else {
				c.NO_DToB();
			}

			continue loop;
		} while(true);
	}
}
