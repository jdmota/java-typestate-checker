package demos.Traversal;

/*
	Tree:

	19
		12
			1
				-
				8
			5
				3
				-
		7
			10
				13
				14
			11
				15
				16
*/

class Run {
	public static void main(String[] args) {

		Node n = new Node(
					new Node(
						new Node(
							null,
							new Node(
								null,
								null,
								8), 
							1),
						new Node(
							new Node(
								null, 
								null, 
								3),
							null,
							5),
						12),
					new Node(
						new Node(
							new Node(null, null, 13),
							new Node(null, null, 14),
							10),
						new Node(
							new Node(null, null, 15),
							new Node(null, null, 16),
							11),
						7),
					19);

		Thread t1 = new Thread(new A(2001, 2002, n));
		Thread t2 = new Thread(new B(2001, 2003));
		Thread t3 = new Thread(new C(2002, 2003));

		t1.start();
		t2.start();
		t3.start();
	}
}
