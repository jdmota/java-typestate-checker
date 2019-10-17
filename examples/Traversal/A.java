package demos.Traversal;

class A implements Runnable {
	int Bport, Cport;
	private Node node;

	A(int Bport, int Cport, Node node) {
		this.Bport = Bport;
		this.Cport = Cport;
		this.node = node;
	}

	public void run() {
		Node queue[] = new Node[100];
		queue[0] = node;
		int head = 1; int tail = 0;

		boolean bflag = true; boolean cflag = true;

		ARole a = new ARole(Bport, Cport);

		loop: do {
			// get from queue
			if(queue[tail] != null) {
				node = queue[tail++];
				bflag = false; cflag = false;
				System.out.println("A: " + node.get());
			}
			else {
				node = null;
			}

			if(node != null && (bflag == false || cflag == false)) {
				if(node.left() != null) {
					a.DATAToB(); a.nodeToB(node.left());
					bflag = false;
				}
				else {
					a.NO_DToB();
				}

				if(node.right() != null) {
					a.DATAToC(); a.nodeToC(node.right());
					cflag = false;
				}
				else {
					a.NO_DToC();
				}

				switch(a.choiceFromB()) {
					case DATA:
						queue[head++] = a.nodeFromB(); //put in a stack
						break;
					case NO_D:
						break;
					case END:
						bflag = true;
						//set a flag
						break;
				}

				switch(a.choiceFromC()) {
					case DATA:
						queue[head++] = a.nodeFromC(); //put in a stack
						break;
					case NO_D:
						break;
					case END:
						cflag = true;
						//set a flag
						break;
				}
				continue loop;

			}
			else {
				a.ENDToB(); a.ENDToC();
				break loop;
			}
		} while(true);
	}
}
